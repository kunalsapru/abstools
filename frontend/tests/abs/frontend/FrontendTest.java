package abs.frontend;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;
import abs.ABSTest;
import abs.frontend.analyser.SemanticErrorList;
import abs.frontend.ast.AssignStmt;
import abs.frontend.ast.CaseBranch;
import abs.frontend.ast.CaseExp;
import abs.frontend.ast.ClassDecl;
import abs.frontend.ast.Decl;
import abs.frontend.ast.Exp;
import abs.frontend.ast.ExpFunctionDef;
import abs.frontend.ast.ExpressionStmt;
import abs.frontend.ast.FunctionDecl;
import abs.frontend.ast.MainBlock;
import abs.frontend.ast.Model;
import abs.frontend.ast.ParametricFunctionDecl;
import abs.frontend.ast.Pattern;
import abs.frontend.ast.Stmt;
import abs.frontend.ast.VarDeclStmt;
import abs.frontend.parser.Main;
import abs.frontend.typechecker.Type;
import static abs.ABSTest.Config.*;

public class FrontendTest extends ABSTest {

    protected Model assertParseOkStdLib(String s) {
        return assertParse(s, WITH_STD_LIB);
    }

    protected void assertParseFileOk(String fileName, boolean withStdLib) {
        assertParseFileOk(fileName, WITH_STD_LIB);
    }

    protected void assertTypeCheckFileOk(String fileName, boolean withStdLib) {
        assertParseFileOk(fileName, TYPE_CHECK, WITH_STD_LIB);
    }

    protected Exp getFirstExp(String absCode) {
        Model m = assertParse(absCode);
        return getFirstExp(m);
    }

    protected Exp getSecondExp(String absCode) {
        return getSecondExp(assertParse(absCode));
    }

    protected Exp getExp(String absCode, int i) {
        return getExp(assertParse(absCode), i);
    }

    protected Exp getSecondExp(Model m) {
        return getExp(m, 1);
    }

    protected Exp getFirstExp(Model m) {
        return getExp(m, 0);
    }

    protected Exp getExp(Model m, int i) {
        Stmt s = m.getMainBlock().getStmt(i);
        if (s instanceof AssignStmt)
            return ((AssignStmt) s).getValue();
        if (s instanceof ExpressionStmt)
            return ((ExpressionStmt) s).getExp();
        if (s instanceof VarDeclStmt)
            return ((VarDeclStmt) s).getVarDecl().getInitExp();
        throw new IllegalArgumentException();
    }

    protected ClassDecl getFirstClassDecl(Model m) {
        for (Decl d : m.getCompilationUnit(m.getNumCompilationUnit()-1).getModuleDecl(0).getDecls()) {
            if (d instanceof ClassDecl) 
                return (ClassDecl) d;
        }
        throw new IllegalArgumentException("No ClassDecl found");
    }
    
    protected Exp getFirstCaseExpr(Model m) {
        CaseExp ce = (CaseExp) getFirstFunctionExpr(m);
        CaseBranch b = ce.getBranch(0);
        return b.getRight();
    }

    protected Exp getSecondCaseExpr(Model m) {
        CaseExp ce = (CaseExp) getFirstFunctionExpr(m);
        CaseBranch b = ce.getBranch(1);
        return b.getRight();
    }

    protected Pattern getFirstCasePattern(Model m) {
        CaseExp ce = (CaseExp) getFirstFunctionExpr(m);
        CaseBranch b = ce.getBranch(0);
        return b.getLeft();
    }
    
    protected Decl getLastDecl(Model m, Class<?> clazz) {
        Decl lastMatching = null;
        for (Decl d : m.getDecls()) {
            if (clazz.isInstance(d)) {
                lastMatching = d;
            }
        }
        if (lastMatching == null)
            throw new IllegalArgumentException("The model does not contain any " + clazz.getSimpleName());
        else
            return lastMatching;
    }

    protected FunctionDecl getLastFunctionDecl(Model m) {
        return (FunctionDecl) getLastDecl(m, FunctionDecl.class);
    }

    protected ParametricFunctionDecl getLastParametricFunctionDecl(Model m) {
        return (ParametricFunctionDecl) getLastDecl(m, ParametricFunctionDecl.class);
    }

    protected Exp getFirstFunctionExpr(Model m) {
        return ((ExpFunctionDef) getLastFunctionDecl(m).getFunctionDef()).getRhs();
    }

    protected Type getTypeOfFirstAssignment(Model m) {
        for (Stmt s : m.getMainBlock().getStmts()) {
            if (s instanceof AssignStmt) {
                AssignStmt as = (AssignStmt) s;
                return as.getValue().getType();
            } else if (s instanceof VarDeclStmt) {
                VarDeclStmt vd = (VarDeclStmt) s;
                if (vd.getVarDecl().hasInitExp()) {
                    return vd.getVarDecl().getInitExp().getType();
                }
            }
        }
        return null;
    }

    protected void assertNoTypeErrorsNoLib(String absCode) {
        assertTypeErrors(absCode, new Config[0]);
    }

    protected void assertNoTypeErrors(String absCode) {
        assertTypeErrors(absCode, WITH_STD_LIB);
    }

    protected void assertTypeErrors(String absCode) {
        assertTypeErrors(absCode, EXPECT_TYPE_ERROR, WITH_STD_LIB);
    }

    protected void assertTypeErrors(String absCode, Config... config) {
        Model m = assertParse(absCode, config);
        String msg = "";
        SemanticErrorList l = m.typeCheck();
        if (!l.isEmpty()) {
            msg = l.getFirst().getMsgWithHint(absCode);
        }
        assertEquals(msg, isSet(EXPECT_TYPE_ERROR, config), !l.isEmpty());
    }

}
