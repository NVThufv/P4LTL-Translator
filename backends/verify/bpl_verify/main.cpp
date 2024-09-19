/*
Copyright 2013-present Barefoot Networks, Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

#include <stdio.h>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>

#include "ir/ir.h"
#include "ir/json_loader.h"
#include "lib/gc.h"
#include "lib/crash.h"
#include "lib/nullstream.h"
#include "backends/verify/translate/options.h"
#include "backends/verify/translate/version.h"
#include "backends/verify/translate/translate.h"
#include "backends/verify/translate/analyzer.h"
#include "backends/verify/translate/bmv2.h"
#include "frontends/common/applyOptionsPragmas.h"
#include "frontends/common/parseInput.h"
#include "frontends/p4/frontend.h"
#include "frontends/parsers/p4ltl/p4ltlast.hpp"
#include "frontends/parsers/p4ltl/p4ltlparser.hpp"
#include "frontends/parsers/p4ltl/p4ltllexer.hpp"
#include <time.h>

int main(int argc, char *const argv[]) {
    clock_t program_start = clock(), program_end;
    double program_cpu_time_used;
    setup_gc_logging();
    setup_signals();

    AutoCompileContext autoP4VerifyContext(new P4VerifyContext);
    auto& options = P4VerifyContext::get().options();
    options.langVersion = CompilerOptions::FrontendVersion::P4_16;
    options.compilerVersion = P4VERIFY_VERSION_STRING;

    if (options.process(argc, argv) != nullptr) {
            if (options.loadIRFromJson == false)
                    options.setInputFile();
    }
    if (::errorCount() > 0)
        return 1;
    const IR::P4Program *program = nullptr;
    auto hook = options.getDebugHook();
    if (options.loadIRFromJson == false) {
        program = P4::parseP4File(options);
        // std::cout << "parse time " << ((double) (clock() - program_start)) / CLOCKS_PER_SEC << " s\n";
        if (program == nullptr || ::errorCount() > 0)
            return 1;
        try {
            P4::P4COptionPragmaParser optionsPragmaParser;
            program->apply(P4::ApplyOptionsPragmas(optionsPragmaParser));

            P4::FrontEnd frontend;
            frontend.addDebugHook(hook);
            program = frontend.run(options, program);
        } catch (const std::exception &bug) {
            std::cerr << bug.what() << std::endl;
            return 1;
        }
        if (program == nullptr || ::errorCount() > 0)
            return 1;
    } else{
        std::ifstream json(options.file);
        if (json) {
            JSONLoader loader(json);
            const IR::Node* node = nullptr;
            loader >> node;
            if (!(program = node->to<IR::P4Program>()))
                error(ErrorType::ERR_INVALID, "%s is not a P4Program in json format", options.file);
        } else {
            error(ErrorType::ERR_IO, "Can't open %s", options.file); }
    }

    clock_t backend_start, backend_end;
    double backend_cpu_time_used;
    backend_start = clock();

    std::ifstream bmv2cmds(options.cmdFile);
    BMV2CmdsAnalyzer* bMV2CmdsAnalyzer = nullptr;
    if(bmv2cmds){
        try{
            bMV2CmdsAnalyzer = new BMV2CmdsAnalyzer(&bmv2cmds);
        } catch (const char* msg) {
            std::cerr << msg << std::endl;
            return 1;
        }
    }

    std::ostream* out = openFile(options.outputBplFile, false);
    
    Translator translator(*out, options, bMV2CmdsAnalyzer);

    if(options.p4ltlSpec){
        std::ifstream fin(options.p4ltlFile);
        
        if(fin){
            std::string s;
            while(getline(fin, s)){
                cstring key = nullptr;
                // std::cout << s << std::endl;
                for(int i = 0; i < P4LTL_KEYS.size(); i++){
                    int idx = s.find(P4LTL_KEYS[i]);
                    if(idx != -1){
                        s = s.substr(idx+P4LTL_KEYS[i].size());
                        key = P4LTL_KEYS[i];
                        break;
                    }
                }
                if(key == nullptr) continue;
                if(key == P4LTL_KEYS_VAR){
                    translator.setP4LTLFreeVars(s);
                    continue;
                }
                // reg write
                if(key == P4LTL_KEYS_REG_WRITE){
                    translator.addRegWrite(s);
                    continue;
                }

                // for CPI_SIMP
                if(key == P4LTL_KEYS_CPI_SIMP) {
                    std::cout << "Extract origin: " + s << "\n";
                    std::vector<cstring> constraints;
                    int idx = -1;
                    while((idx = s.find(";")) != -1) {
                        constraints.push_back(s.substr(0, idx));
                        s = s.substr(idx + 1);
                    }
                    // action/last constriant is s
                    cstring CPI = "[](AP((true == true";
                    for(auto keyConstraint: constraints) {
                        CPI += " && " + keyConstraint;
                    }
                    CPI += ") ==> " + s + "))";
                    std::cout << "Extracted: " + CPI + "\n";
                    // reduce to CPI_SPEC
                    s = CPI;
                    key = P4LTL_KEYS_CPI_SPEC;
                }

                // parse P4LTL
                std::istringstream p4ltlSpec(s);
                P4LTL::Scanner scanner{ p4ltlSpec, std::cerr };
                P4LTL::AstNode* root = nullptr;
                P4LTL::P4LTLParser parser{ scanner, root};
                int result = parser.parse();
                if(result == 0 && root){
                    std::cout << "P4LTL specification size: " << (translator.ltlTranslator)->getSpecSize(root) << std::endl;
                    std::cout << "P4LTL parsing result: ";
                    std::cout << root->toString() << std::endl;
                    translator.setP4LTLSpec(key, root);
                    std::cout << std::endl;
                } else {
                    std::cerr << "ERROR: error when parsing P4LTL: " + s + "\n";
                    std::abort();
                }
            }
        }

        // traverse CPI and collect, map: CPI, CPI[table] = assume condition
        translator.collectCPI();
    }
    if (out != nullptr) {
        translator.translate(program);
        translator.writeToFile();
        out->flush();
        // Analyzer analyzer;
        // analyzer.analyzeP4Program(program);
    } else {
        std::cerr << "WARNING: no output file specified. Only analysis is done. \n";
    }
    backend_end = clock();
    backend_cpu_time_used = ((double) (backend_end - backend_start)) / CLOCKS_PER_SEC;
    program_cpu_time_used = ((double) (backend_end - program_start)) / CLOCKS_PER_SEC;
    // std::cout << "backend done in " << DURATION(front)/1000.0 << " s\n";
    std::cout << "backend cpu time " << backend_cpu_time_used << " s\n";
    std::cout << "program cpu time " << program_cpu_time_used << " s\n";
    return 0;
}