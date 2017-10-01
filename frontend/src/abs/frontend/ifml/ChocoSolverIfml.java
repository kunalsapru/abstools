/**
 * Copyright (c) 2009-2011, The HATS Consortium. All rights reserved. 
 * This file is licensed under the terms of the Modified BSD License.
 */
package abs.frontend.ifml;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import abs.frontend.ast.IfmlBoundaryInt;
import abs.frontend.ast.IfmlBoundaryVal;
import abs.frontend.ast.IfmlCardinality;
import abs.frontend.ast.IfmlConstraint;
import abs.frontend.ast.IfmlGroupDecl;
import abs.frontend.ast.IfmlLimit;

public class ChocoSolverIfml {

    public final Model cs4model;
    public boolean solved = false;
    public boolean newsol = false;
    public final Map<String, IntVar> vars;
    public final Map<String, Integer> defaultvals;
    private List<Constraint> constraints = new ArrayList<Constraint>();
    private List<Constraint> groupConstraints = new ArrayList<Constraint>();
    private List<Constraint> featureConstraints = new ArrayList<Constraint>();
//    private abs.frontend.ast.Model absmodel = new abs.frontend.ast.Model();

    public ChocoSolverIfml() {
        // Build the ChocoSolver4 model
        cs4model = new Model();
        vars = new HashMap<String, IntVar>();
        defaultvals = new HashMap<String, Integer>();
    }

    public ChocoSolverIfml(abs.frontend.ast.Model m) {
        this();
    }

    /** add ChocoSolver4 constraint **/
    public void addConstraint(Constraint c) {
        constraints.add(c);
    }

    /** add ChocoSolver4 constraint **/
    public void addGroupConstraint(Constraint c) {
        groupConstraints.add(c);
    }
    /** add ChocoSolver4 constraint **/
    public void addFeatureConstraint(Constraint c) {
        featureConstraints.add(c);
    }
    private void addIntVar(String name) {
        IntVar v = cs4model.intVar(name, IntVar.MIN_INT_BOUND, IntVar.MAX_INT_BOUND);
        vars.put(name, v);
        defaultvals.put(name,0);
        
    }

    public void addIntVar(String name, int from, int to) {
        IntVar v = cs4model.intVar(name, from, to);// IntVar value is the lower bound.
        vars.put(name, v);
        defaultvals.put(name,from);
    }

    public void addIntVar(String name, int fromto, boolean from) {
        IntVar v;
        if (from) {
            v = cs4model.intVar(name, fromto, IntVar.MAX_INT_BOUND);
        } else {
            v = cs4model.intVar(name, IntVar.MIN_INT_BOUND, fromto);
        }
        vars.put(name, v);
        defaultvals.put(name, fromto);
    }

    public void addIntVar(String name, int[] vals) {
        IntVar v = cs4model.intVar(name, vals);
        vars.put(name, v);
        defaultvals.put(name, vals[0]); // vals has at least 1 element! (by the parser constraints)
    }
    
    public void addBoolVar(String name) {
        IntVar v = cs4model.boolVar(name);
        vars.put(name, v);
        defaultvals.put(name,0);
    }
    
    /** set a bool variable to true **/
    public void forceTrue(String name) {
        IntVar v = cs4model.intVar(name, 1, 1);
        vars.put(name, v);
        defaultvals.put(name, 1);
    }
    
    public IntVar getVar(String var) {
        return vars.get(var);
    }

    public void addSetVar(String name, IfmlBoundaryInt[] bs) {
        int bsize = bs.length - 1;
        int[] vals = new int[bsize];
        // addSetVar only called if bs has only BoundaryVals
        for (int i=0; i < bsize; i++) {
            vals[i] = ((IfmlBoundaryVal) bs[i+1]).getValue(); // drop first value - repeated
        }
        addIntVar(name,vals);
    }
    
    public void addBoundedVar(String name, IfmlBoundaryInt b1, IfmlBoundaryInt b2) {
        if(b1 instanceof IfmlLimit) {
            if(b2 instanceof IfmlLimit) {
                addIntVar(name);
            } else {
                addIntVar(name,((IfmlBoundaryVal) b2).getValue(), false);
            }
        } else if(b2 instanceof IfmlLimit) {
            addIntVar(name,((IfmlBoundaryVal) b1).getValue(), true);
        } else {
            addIntVar(name, ((IfmlBoundaryVal) b1).getValue(), ((IfmlBoundaryVal) b2).getValue());
        }
    }
    
    public List<String> checkSolutionWithErrors(Map<String, Integer> solution, abs.frontend.ast.Model absmodel) {
        List<String> result = new ArrayList<String>();
        for(Map.Entry<String, Integer> entry : solution.entrySet()) {
            String featureName = entry.getKey();
            if(!(featureName.contains("."))) {
                //Get all constraints for this feature
                ArrayList<IfmlConstraint> ifmlFeatureConstraintList = absmodel.getAllFeatureConstraints(featureName);
                //Add feature constraints to featureConstraints list
                
                // Getting group for feature 'featureName'
                IfmlGroupDecl ifmlGroupDecl = absmodel.getIfmlGroupDecl(featureName);
                if(ifmlGroupDecl!=null) {
                    //Get group constraints for this group
                    ArrayList<IfmlConstraint> ifmlGroupConstraintList = absmodel.getAllGroupConstraints(ifmlGroupDecl.getName());
                    //Add group constraints to groupConstraints list
                    ArrayList<IfmlCardinality> ifmlCardinalityList = absmodel.getGroupCardinality(ifmlGroupDecl.getName());
                    if(ifmlCardinalityList.size() > 1){
                        //Show Error for multiple cardinalities
                        result.add("Multiple cardinalities found for group '"+ifmlGroupDecl.getName()+"'.");
                    } else if(ifmlCardinalityList.size() == 1){
                        //Add cardinality constraint to groupConstraints list
                    }
                }
            }
        }
        Solver solver = cs4model.getSolver();
        int val;
        IntVar[] intVars = cs4model.retrieveIntVars(true);
        boolean domainCheckError = false;
        //Check for variable's domain
        for(IntVar var : intVars){
            if(solution.containsKey(var.getName())){
                val = solution.get(var.getName());
                    cs4model.getEnvironment().worldPush();
                        try {
                            var.instantiateTo(val, null);
                            solver.propagate();
                        } catch (ContradictionException e) {
                            solver.getEngine().flush();
                            domainCheckError = true;
                            result.add("Out of domain error for "+var.getName()+" with value "+val);
                        }
                    cs4model.getEnvironment().worldPop();
            }
        }
        if(!domainCheckError) {
            //Check for constraints, only in case of no domain error(s)
            for(Constraint c : constraints) {
                cs4model.post(c);
                for(IntVar var : intVars){
                    if(solution.containsKey(var.getName())){
                        val = solution.get(var.getName());
                        cs4model.getEnvironment().worldPush();
                        try {
                            var.instantiateTo(val, null);
                            solver.propagate();
                        } catch (ContradictionException e) {
                            solver.getEngine().flush();
                            result.add("Constraint failed for "+var.getName()+" with value "+val+" --> "+c.toString());
                        }
                        cs4model.getEnvironment().worldPop();
                    }
                }
                cs4model.unpost(c);
            }
        }
        
        return result;
    }

}