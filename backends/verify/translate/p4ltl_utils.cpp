#include "backends/verify/translate/p4ltl_utils.h"

// bool isAPNode(P4LTL::AstNode* node){
// 	if(dynamic_cast<P4LTL::P4LTLAtomicProposition*>(node) != nullptr)
// 		return true;
// 	return false;
// }


// std::vector<P4LTL::AstNode*> getAllAPs(P4LTL::AstNode* root){
// 	std::vector<P4LTL::AstNode*> aps;
// 	for(auto child: getAllNodes(root)){
// 		if(isAPNode(child)) aps.push_back(child);
// 	}
// 	return aps;
// }

void P4LTLTranslator::getAllNodes(std::vector<P4LTL::AstNode*>& nodes, P4LTL::AstNode* root){
	nodes.push_back(root);
    for(auto child: root->getOutgoingNodes()){
        getAllNodes(nodes, child);
    }
}

std::vector<P4LTL::AstNode*> P4LTLTranslator::getAllNodes(P4LTL::AstNode* root){
	std::vector<P4LTL::AstNode*> nodes;
	getAllNodes(nodes, root);
	return nodes;
}


std::set<cstring> P4LTLTranslator::getOldExprs(P4LTL::AstNode* root){
	std::set<cstring> res;
	for(auto node:getAllNodes(root)){
		if(auto oldExpression = dynamic_cast<P4LTL::OldExpression*>(node)){
			res.insert(oldExpression->getValue()->toString());
		}
	}
	return res;
}

std::map<cstring, std::set<cstring>> P4LTLTranslator::getOldArrays(P4LTL::AstNode* root){
	std::map<cstring, std::set<cstring>> res;
	for(auto node:getAllNodes(root)){
		if(auto oldExpression = dynamic_cast<P4LTL::OldExpression*>(node)){
			if(auto arrayAccess = dynamic_cast<P4LTL::ArrayAccessExprssion*>(oldExpression->getValue())){
				auto nodes = arrayAccess->getOutgoingNodes();
				cstring name = translateP4LTL(nodes[0]);
				cstring index = translateP4LTL(nodes[1]);
				if(isFreeVariable(index)) index = "_p4ltl_free_"+index;
				res[name].insert(index);
			}
		}
	}
	return res;
}

bool P4LTLTranslator::isActionApplied(P4LTL::AstNode* root, cstring action){
	for(auto node:getAllNodes(root)){
		if(auto apply = dynamic_cast<P4LTL::Apply*>(node)){
			if(!apply->getAction().empty()){
				cstring applyAction = apply->getAction();
				if(action == applyAction) return true;
			}
		}
	}
	return false;
}

std::set<cstring> P4LTLTranslator::getCPITable(P4LTL::AstNode* root){
	std::set<cstring> result;
	for(auto node:getAllNodes(root)){
		if(auto apply = dynamic_cast<P4LTL::Apply*>(node)){
			result.insert(apply->getTable());
		}
	}
	return result;
}

cstring P4LTLTranslator::translateCPI(P4LTL::AstNode* node) {
	if(auto unTempOp = dynamic_cast<P4LTL::UnaryTemporalOperator*>(node)){
		if(auto ap = dynamic_cast<P4LTL::P4LTLAtomicProposition*>(unTempOp->getChild()))
			return translateP4LTL(ap->getProposition());
	} 
	std::cerr << "ERROR: not correct CPI syntax. Should be G(AP(CPI)): " + translateP4LTL(node) << "\n";
	std::abort();
}

// extract key ==> action condition
// Return: pair<key, action> if succeeded else (false, false)
std::pair<cstring, cstring> P4LTLTranslator::extractCPI(P4LTL::AstNode* node) {
	if(auto unTempOp = dynamic_cast<P4LTL::UnaryTemporalOperator*>(node)){
		if(auto ap = dynamic_cast<P4LTL::P4LTLAtomicProposition*>(unTempOp->getChild()))
			if(auto impl = dynamic_cast<P4LTL::BinaryPredicateOperator*>(ap->getProposition()))
				if(impl->getOpType() == P4LTL::BinaryPredicateOperator::BinaryPredicateOperatorType::Implies)
					return std::pair<cstring, cstring> (translateP4LTL(impl->getLeft()), translateP4LTL(impl->getRight()));
	} 
	return std::pair<cstring, cstring> ("false", "false");
}

cstring P4LTLTranslator::translateP4LTL(P4LTL::AstNode* node){
	if(auto binOpNode = dynamic_cast<P4LTL::BinOpNode*>(node)){
		return translateP4LTL(binOpNode);
	}
	else if(auto uOpNode = dynamic_cast<P4LTL::UOpNode*>(node)){
		return translateP4LTL(uOpNode);
	}
	else if(auto ap = dynamic_cast<P4LTL::P4LTLAtomicProposition*>(node)){
		return translateP4LTL(ap);
	}
	else if(auto predicate = dynamic_cast<P4LTL::Predicate*>(node)){
		return translateP4LTL(predicate);
	}
	else if(auto intLiteral = dynamic_cast<P4LTL::IntLiteral*>(node)){
		return translateP4LTL(intLiteral);
	}
	else if(auto boolLiteral = dynamic_cast<P4LTL::BooleanLiteral*>(node)){
		return translateP4LTL(boolLiteral);
	}
	else if(auto name = dynamic_cast<P4LTL::Name*>(node)){
		return translateP4LTL(name);
	}
	else if(auto key = dynamic_cast<P4LTL::Key*>(node)){
		return translateP4LTL(key);
	}
	else if(auto arrayAccess = dynamic_cast<P4LTL::ArrayAccessExprssion*>(node)){
		return translateP4LTL(arrayAccess);
	}
	else if(auto oldExpression = dynamic_cast<P4LTL::OldExpression*>(node)){
		return "_old_"+translateP4LTL(oldExpression->getValue());
	}
	else {
		return node->toString();
	}
}

cstring P4LTLTranslator::translateP4LTL(P4LTL::BinOpNode* node){
	if(auto binTempOp = dynamic_cast<P4LTL::BinaryTemporalOperator*>(node)){
		// std::cout << "BinaryTemporalOperator" << std::endl << node->getOp() << std::endl;
		return "("+translateP4LTL(binTempOp->getLeft())+binTempOp->getOp()
				+translateP4LTL(binTempOp->getRight())+")";
	}
	else if(auto extendedCompOp = dynamic_cast<P4LTL::ExtendedComparativeOperator*>(node)){
		return "("+translateP4LTL(extendedCompOp->getLeft())+extendedCompOp->getOp()
				+translateP4LTL(extendedCompOp->getRight())+")";
	}
	else if(auto binPredOp = dynamic_cast<P4LTL::BinaryPredicateOperator*>(node)){
		return "("+translateP4LTL(binPredOp->getLeft())+binPredOp->getOp()
				+translateP4LTL(binPredOp->getRight())+")";
	}
	// + - *
	else if(auto binTermOp = dynamic_cast<P4LTL::BinaryTermOperator*>(node)){
		cstring expr = binTermOp->toString();
		if(alreadyDeclared(expr)){
			return getCacheVariable(expr);
		}

		cstring variable = TempVariable::getPrefix("_p4ltl_");
		addVariable(variable);

		cache[expr] = variable;

		addDeclaration("\nvar "+variable+":int;\n");

		cstring left = translateP4LTL(binTermOp->getLeft());
		cstring right = translateP4LTL(binTermOp->getRight());
		int sizeLeft = getSize(left), sizeRight = getSize(right);
		if(sizeLeft != -1 || sizeRight != -1){
			if(sizeLeft == -1) sizeLeft = sizeRight;
			else if(sizeRight == -1) sizeRight = sizeLeft;
			
			if(sizeLeft != sizeRight){
				std::cout << "ERROR: " << left << binTermOp->getOp() << right 
					<< " is not legal." << std::endl;
			}
			else{
				sizes[variable] = sizeLeft;
				cstring size = p4Translator->toString(sizeLeft);
				cstring powerFunc = "power_2_"+size+"()";
            	cstring funcName = "";
            	if(binTermOp->getOp() == " + ") funcName = "add.bv"+size;
            	else if(binTermOp->getOp() == " - ") funcName = "sub.bv"+size;
            	else if(binTermOp->getOp() == " * ") funcName = "mul.bv"+size;
            	cstring function = "function {:inline true} "+funcName+"(left:int, right:int) : int{("+
                	"(left\%"+powerFunc+")+(right\%"+powerFunc+"))\%"+powerFunc+"}\n";
            	p4Translator->addFunction(funcName, function);
            	addStatement(variable+" := "+funcName+"("+left+", "+right+");\n");
			}
		}
		else{
			addStatement(variable+" := "+left+binTermOp->getOp()+right+";\n");
		}
		return variable;
	}
	else return node->toString();
}

cstring P4LTLTranslator::translateP4LTL(P4LTL::UOpNode* node){
	if(auto unTempOp = dynamic_cast<P4LTL::UnaryTemporalOperator*>(node)){
		return "("+unTempOp->getOp()+"("+translateP4LTL(unTempOp->getChild())+"))";
	}
	else if(auto unPredOp = dynamic_cast<P4LTL::UnaryPredicateOperator*>(node)){
		return "("+unPredOp->getOp()+"("+translateP4LTL(unPredOp->getChild())+"))";
	}
	else return node->toString();
}

cstring P4LTLTranslator::translateP4LTL(P4LTL::P4LTLAtomicProposition* node){
	return "AP("+translateP4LTL(node->getProposition())+")";
}

cstring P4LTLTranslator::translateP4LTL(P4LTL::Predicate* node){
	if(auto drop = dynamic_cast<P4LTL::Drop*>(node)){
		return drop->toString();
	}
	else if(auto forward = dynamic_cast<P4LTL::Forward*>(node)){
		return forward->toString();
	}
	else if(auto valid = dynamic_cast<P4LTL::Valid*>(node)){
		return valid->getHeader()+".valid == true";
	}
	else if(auto apply = dynamic_cast<P4LTL::Apply*>(node)){
		// change to basic translation
		if(apply->getAction().empty())
			return apply->getTable()+".isApplied";
		else
			return apply->getTable()+"."+apply->getAction()+".isApplied";
	}
	else return node->toString();
}

cstring P4LTLTranslator::translateP4LTL(P4LTL::IntLiteral* node){
	return node->toString();
}

cstring P4LTLTranslator::translateP4LTL(P4LTL::BooleanLiteral* node){
	return node->toString();
}

cstring P4LTLTranslator::translateP4LTL(P4LTL::Name* node){
	{
		cstring res = node->toString();
		if(isFreeVariable(res)){
			return freeVars[res];
		}
		else return res;
	}
}

cstring P4LTLTranslator::translateP4LTL(P4LTL::Key* node){
	return node->getTable()+"."+node->getKey();
}

cstring P4LTLTranslator::translateP4LTL(P4LTL::ArrayAccessExprssion* node){
	cstring res = "";
	auto nodes = node->getOutgoingNodes();
	res = translateP4LTL(nodes[0]);
    for(int i = 1; i < nodes.size(); ++i){
    	cstring cont = translateP4LTL(nodes[i]);
    	if(isFreeVariable(cont)) cont = "_p4ltl_free_"+cont;
        res += "[" + cont + "]";
    }
	return res;
}

int P4LTLTranslator::getSize(cstring variable){
	if(p4Translator->getSize(variable) != -1){
		return p4Translator->getSize(variable);
	}
	else if(sizes.find(variable) != sizes.end()){
		return sizes[variable];
	}
	else return -1;
}

std::map<cstring, cstring>  P4LTLTranslator::getFreeVariables(){
	return freeVars;
}

bool P4LTLTranslator::isFreeVariable(cstring variable){
	return freeVars.find(variable) != freeVars.end();
}

bool P4LTLTranslator::isBvType(cstring type){
	std::string str = type.c_str();
	if(str.size() < 3) return false;
	if(str[0]=='b' && str[1]=='v'){
		return isNumber(str.substr(2));
	}
	return false;
}

int P4LTLTranslator::getBvLength(cstring type){
	if(isBvType(type)){
		std::string str = type.c_str();
		return atoi(str.substr(2).c_str());
	}
	return -1;
}

void P4LTLTranslator::addFreeVariable(cstring variable){
	std::string str = variable.c_str();
	int idx = str.find(':');
	if(idx == -1){
		std::cout << "ERROR: free variable must be declared with TYPE.\n" 
			<< str << std::endl; 
		std::abort();
	}
	cstring name, type;
	name = str.substr(0, idx);
	type = str.substr(idx+1);
	if(type != "bool" && type != "int" && !isBvType(type)){
		std::cout << "ERROR: Unsupported type \""<< type << "\"" << std::endl; 
		std::abort();
	}
	freeVars[name] = "_p4ltl_free_"+name;
	if(isBvType(type)){
		int length = getBvLength(type);
		sizes["_p4ltl_free_"+name] = length;
		addDeclaration("\nvar "+freeVars[name]+":int;\n");
		// TODO: add assumptions for bv
	}
	else{
		addDeclaration("\nvar "+freeVars[name]+":"+type+";\n");
	}
}

void P4LTLTranslator::createFreeVariables(cstring decl){
	std::string str = decl.c_str();
	str.erase(std::remove_if(str.begin(), str.end(), [](char c) {
        return std::isspace(static_cast<unsigned char>(c));
    }), str.end());

	int start = 0, end = 0;
	end = str.find(',', start);
	while(end != -1){
		addFreeVariable(str.substr(start, end-start));
		start = end+1;
		end = str.find(',', start);
	}
	if(start < str.length()){
		addFreeVariable(str.substr(start));
	}
}

/*
	Variables:  additional variables
	Statements:  statements for main Procedure
	Declarations:  declarations for variables
*/
std::vector<cstring> P4LTLTranslator::getVariables(){
	return vars;
}

void P4LTLTranslator::addVariable(cstring variable){
	vars.push_back(variable);
}

std::vector<cstring> P4LTLTranslator::getStatements(){
	return stmts;
}

void P4LTLTranslator::addStatement(cstring stmt){
	stmts.push_back(stmt);
}

std::vector<cstring> P4LTLTranslator::getDeclarations(){
	return declarations;
}

void P4LTLTranslator::addDeclaration(cstring declaration){
	declarations.push_back(declaration);
}

bool P4LTLTranslator::alreadyDeclared(cstring expr){
	if(cache.find(expr) != cache.end()) return true;
	return false;
}

cstring P4LTLTranslator::getCacheVariable(cstring expr){
	if(alreadyDeclared(expr)){
		return cache[expr];
	}
	return nullptr;
}

int P4LTLTranslator::getSpecSize(P4LTL::AstNode* root)
{
	int result = 0;
	if(root) {
		result = 1;
		for(auto child: root->getOutgoingNodes())
		{
			result += getSpecSize(child);
		}
	}
	return result;
}

CPIRule* P4LTLTranslator::analyzeRule(P4LTL::AstNode* root){
	CPIRule* rule;
	cstring table = "";
	cstring action = "";
	cstring key = "";
	cstring value = "";
	std::vector<cstring> params;
	if(auto temporal = dynamic_cast<P4LTL::UnaryTemporalOperator*>(root)){
		if(auto ap = dynamic_cast<P4LTL::P4LTLAtomicProposition*>(temporal->getChild())){
			if(auto binOp = dynamic_cast<P4LTL::BinaryPredicateOperator*>(ap->getProposition())){
				if(binOp->getOp() == " ==> "){
					if(auto match = dynamic_cast<P4LTL::BinaryPredicateOperator*>(binOp->getLeft())){
						if(match->getOp() == " && "){
							if(auto tableApply = dynamic_cast<P4LTL::Apply*>(match->getLeft())){
								table = tableApply->getTable();
								// std::cout << "##Table: " << table << std::endl;;
							}
							if(auto keyValue = dynamic_cast<P4LTL::ExtendedComparativeOperator*>(match->getRight())){
								if(auto keyExpr = dynamic_cast<P4LTL::Key*>(keyValue->getLeft())){
									key = keyExpr->getKey();
								}
								value = keyValue->getOp() + translateP4LTL(keyValue->getRight());
								// std::cout << key << value << std::endl;
							}
							// TODO: multiple rules
						}
					}
				}
				if(auto actionApply = dynamic_cast<P4LTL::Apply*>(binOp->getRight())){
					action = actionApply->getAction();
					// std::cout << "##Action: " << action << std::endl;
				}
				else if(auto actionParam = dynamic_cast<P4LTL::BinaryPredicateOperator*>(binOp->getRight())){
					if(auto actionApply2 = dynamic_cast<P4LTL::Apply*>(actionParam->getLeft())){
						action = actionApply2->getAction();
					}
					P4LTL::AstNode* node = actionParam->getRight();
					while(dynamic_cast<P4LTL::BinaryPredicateOperator*>(node) != nullptr){
						auto item =dynamic_cast<P4LTL::BinaryPredicateOperator*>(node);
						if(auto left = dynamic_cast<P4LTL::ExtendedComparativeOperator*>(item->getLeft())){
							if(left->getOp() == " == "){
								params.push_back(left->getRight()->toString());
							}
						}
						node = item->getRight();
					}
					if(auto nodeLeft = dynamic_cast<P4LTL::ExtendedComparativeOperator*>(node)){
						if(nodeLeft->getOp() == " == "){
							params.push_back(nodeLeft->getRight()->toString());
						}
					}
				}
			}
		}
	}
	if(table != "" && action != "" && key != "" && value != ""){
		rule = new CPIRule();
		rule->setTable(table);
		rule->setAction(action);
		rule->addKey(key, value);
		for(cstring param:params) rule->addParam(param);
	}
	return rule;
}