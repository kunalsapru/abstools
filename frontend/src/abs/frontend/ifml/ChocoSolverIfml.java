/**
 * Copyright (c) 2009-2011, The HATS Consortium. All rights reserved. 
 * This file is licensed under the terms of the Modified BSD License.
 */
package abs.frontend.ifml;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import org.chocosolver.solver.Cause;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.BoolVar;
import org.chocosolver.solver.variables.IntVar;

import abs.frontend.ast.IfmlAllOf;
import abs.frontend.ast.IfmlBoundaryInt;
import abs.frontend.ast.IfmlBoundaryVal;
import abs.frontend.ast.IfmlCRange;
import abs.frontend.ast.IfmlCardinality;
import abs.frontend.ast.IfmlConstraint;
import abs.frontend.ast.IfmlExcludes;
import abs.frontend.ast.IfmlFeatVar;
import abs.frontend.ast.IfmlGroupDecl;
import abs.frontend.ast.IfmlIfIn;
import abs.frontend.ast.IfmlIfOut;
import abs.frontend.ast.IfmlLimit;
import abs.frontend.ast.IfmlMinim;
import abs.frontend.ast.IfmlOpt;
import abs.frontend.ast.IfmlRequires;

public class ChocoSolverIfml {

    public final Model cs4model;
    public boolean solved = false;
    public boolean newsol = false;
    public final Map<String, IntVar> vars;
    public final Map<String, Integer> defaultvals;
    private List<Constraint> constraints = new ArrayList<Constraint>();

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
    
    /**
     * This function takes bounded integer variables and creates IntVar variables for choco solver model
     * @param name of the variable
     * @param b1 First boundary variable
     * @param b2 Second boundary variable
     */
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
    
    /**
     * This method checks for all errors in ABS program, including domain and constraint errors
     * @param solution map created by user in the ABS program
     * @param absmodel
     * @return a list of domain/constraint errors
     */
    public List<String> checkSolutionWithErrors(Map<String, Integer> solution, abs.frontend.ast.Model absmodel) {
        List<String> result = new ArrayList<String>();//List to store all errors
        //Add domain errors to list
        result.addAll(getDomainErrorList(solution));

        //Add constraints for features and groups selected by user
        addConstraintsForFeaturesAndGroups(solution, absmodel);

        //Add, all constraint failure errors to list, only when there are no domain errors
        if(result.isEmpty()) {
            result.addAll(checkAllIfmlConstraints(solution, absmodel));
        }
        return removeDuplicateFromList(result);
    }
    
    
    /**
     * This method checks for domain errors for all attributes selected inside a feature by the user
     * @param solution map created by user in the ABS program
     * @return a list of domain errors
     */
    private List<String> getDomainErrorList(Map<String, Integer> solution) {
        List<String> result = new ArrayList<String>();
        Solver solver = cs4model.getSolver();
        int val = 0;
        IntVar[] intVars = cs4model.retrieveIntVars(true);
        //Check for variable's domain
        for(IntVar var : intVars){
            cs4model.getEnvironment().worldPush();
            try {
                solver.propagate();
                if(solution.containsKey(var.getName())){
                    val = solution.get(var.getName());
                                var.instantiateTo(val, null);
                } else {
                    if(defaultvals.get(var.getName()) != null) {
                        val = defaultvals.get(var.getName());
                        var.instantiateTo(val, Cause.Null);
                    }
                }
                solver.propagate();
            } catch (ContradictionException e) {
                solver.getEngine().flush();
                result.add("Out of domain error for "+var.getName()+" with value "+val);
            }
            cs4model.getEnvironment().worldPop();
        }
        return removeDuplicateFromList(result);
    }

    /**
     * This function adds all constraints relevant for features and groups selected by user in ABS program.
     * A group is automatically selected, if any of it's feature is selected 
     * @param solution map created by user in ABS program
     * @param absmodel
     */
    private void addConstraintsForFeaturesAndGroups(Map<String, Integer> solution, abs.frontend.ast.Model absmodel) {

        ArrayList<String> groupListForProduct = new ArrayList<String>();
        for(Map.Entry<String, Integer> entry : solution.entrySet()) {
            String featureName = entry.getKey();
            if(!(featureName.contains("."))) {
                // Getting group for feature 'featureName'
                IfmlGroupDecl ifmlGroupDecl = absmodel.getIfmlGroupDecl(featureName);
                if(ifmlGroupDecl!=null) {
                    if(!(groupListForProduct.contains(ifmlGroupDecl.getName()))){
                        groupListForProduct.add(ifmlGroupDecl.getName());
                    }
                }
                //Get all constraints for this feature
                ArrayList<IfmlConstraint> ifmlFeatureConstraintList = absmodel.getAllFeatureConstraints(featureName);
                //Add feature constraints to featureConstraints list
                if(!(ifmlFeatureConstraintList.isEmpty())) {
                    addIfmlConstraints(ifmlFeatureConstraintList);
                }
            }
        }
        //Add Group constraints 
        for(String groupName: groupListForProduct) {
            //Add Cardinality constraints for this group
            IfmlGroupDecl ifmlGroupDecl = absmodel.getIfmlGroupDeclByGroupName(groupName);
            if(ifmlGroupDecl != null) {
                IfmlCardinality ifmlCardinality = absmodel.getGroupCardinality(ifmlGroupDecl.getName());
                if(ifmlCardinality != null){
                    //Add cardinality constraint here
                    addCardinalityConstraint(ifmlGroupDecl, ifmlCardinality);
                }

                //Get group constraints for this group
                ArrayList<IfmlConstraint> ifmlGroupConstraintList = absmodel.getAllGroupConstraints(ifmlGroupDecl.getName());
                //Now add IfmlConstraints to constraints list
                if(!(ifmlGroupConstraintList.isEmpty())) {
                    addIfmlConstraints(ifmlGroupConstraintList);
                }
            }
        }        
    }

    /**
     * This function adds all IfmlConstraints for features and groups in the constraints list
     * @param ifmlConstraintList list containing IfmlConstraint objects
     */
    private void addIfmlConstraints(ArrayList<IfmlConstraint> ifmlConstraintList) {
        //IfmlOpt constraint is handled while checking solution
        IntVar[] featureVars = cs4model.retrieveIntVars(true);
        for(IfmlConstraint ifmlConstraint : ifmlConstraintList) {
            //Adding Requires constraint
            if(ifmlConstraint instanceof IfmlRequires) {
                IfmlRequires ifmlRequires = (IfmlRequires)ifmlConstraint;
                for(IfmlFeatVar ifmlFeatVar : ifmlRequires.getIfmlFeatVarList()){
                    String featName = ifmlFeatVar.getIfmlFName();
                    for(IntVar featureVar : featureVars){
                        if(featureVar.getName().equals(featName)) {
                            addConstraint(cs4model.arithm(featureVar,"=",1));
                        }
                    }
                    
                }
            } else if(ifmlConstraint instanceof IfmlExcludes){//Adding Excludes constraint
                IfmlExcludes ifmlExcludes = (IfmlExcludes)ifmlConstraint;
                for(IfmlFeatVar ifmlFeatVar : ifmlExcludes.getIfmlFeatVarList()){
                    String featName = ifmlFeatVar.getIfmlFName();
                    for(IntVar featureVar : featureVars){
                        if(featureVar.getName().equals(featName)) {
                            addConstraint(cs4model.arithm(featureVar,"=",0));
                        }
                    }
                    
                }
            } else if(ifmlConstraint instanceof IfmlIfIn){
                System.out.println(ifmlConstraint.toString());
            } else if (ifmlConstraint instanceof IfmlIfOut){
                
            }
        }
    }

    /**
     * @param solution map created by user in ABS program
     * @param absmodel 
     * @return List of failed constraint(s)
     */
    private List<String> checkAllIfmlConstraints(Map<String, Integer> solution, abs.frontend.ast.Model absmodel){
        Solver solver = cs4model.getSolver();
        List<String> result = new ArrayList<>();
        IntVar[] intVars = cs4model.retrieveIntVars(true);
        int val=0;
        try {
            solver.propagate();
        } catch (ContradictionException e1) {
            result.add("Exception while propagating solver --> "+e1.toString());
        } catch(Exception e2){
            result.add("Exception while propagating solver --> "+e2.toString());
        }
        for(Constraint c : constraints) {
            cs4model.post(c);
            cs4model.getEnvironment().worldPush();
            for(IntVar var : intVars){
                try {
                    solver.propagate();
                    if(solution.containsKey(var.getName())){
                        val = solution.get(var.getName());
                        var.instantiateTo(val, Cause.Null);
                    } else {
                        boolean optFeatureFlag = false;
                        String featureName = var.getName();
                        if(!(featureName.contains("."))) {
                            //Get all constraints for this feature
                            ArrayList<IfmlConstraint> ifmlFeatureConstraintList = absmodel.getAllFeatureConstraints(featureName);
                            //Add feature constraints to featureConstraints list
                            if(!(ifmlFeatureConstraintList.isEmpty())) {
                                for(IfmlConstraint ifmlConstraint : ifmlFeatureConstraintList) {
                                    if(ifmlConstraint instanceof IfmlOpt) {
                                        var.instantiateTo(1, Cause.Null); //Set optional feature value to true
                                        optFeatureFlag = true;
                                    }
                                }
                            }
                        }

                        if(!optFeatureFlag && defaultvals.get(var.getName()) != null) {
                            val = defaultvals.get(var.getName());
                            var.instantiateTo(val, Cause.Null);
                        }
                    }
                    solver.propagate();
                } catch (ContradictionException e) {
                    solver.getEngine().flush();
                    result.add(c.toString());
                } catch (Exception e1) {
                    solver.getEngine().flush();
                    result.add(c.toString());
                }
            }
            cs4model.getEnvironment().worldPop();
            cs4model.unpost(c);
        }
        
        return removeDuplicateFromList(result);
    }

    /**
     * This function adds cardinality constraints like allof, oneof to groups
     * @param ifmlGroupDecl
     * @param ifmlCardinality
     * @param solution map created by user in ABS program
     */
    private void addCardinalityConstraint(IfmlGroupDecl ifmlGroupDecl, IfmlCardinality ifmlCardinality) {
        //Get all features inside a group
        BoolVar[] allFeaturesInGroup = getAllFeaturesInGroup(ifmlGroupDecl);
        //Applying cardinality constraints
        if(ifmlCardinality instanceof IfmlAllOf){
            //Apply allof cardinality
          //Every group must have atleast one feature
            addConstraint(cs4model.sum(allFeaturesInGroup, "=" , allFeaturesInGroup.length));
        } else if(ifmlCardinality instanceof IfmlMinim){
            //Apply [From..*] cardinality
            addConstraint(cs4model.sum(allFeaturesInGroup, ">=" , ((IfmlMinim) ifmlCardinality).getIfmlCFrom()));
        } else if(ifmlCardinality instanceof IfmlCRange){
            if(((IfmlCRange) ifmlCardinality).getIfmlCFrom() == 1 && ((IfmlCRange) ifmlCardinality).getIfmlCTo() == 1){
                //Apply oneof cardinality
                addConstraint(cs4model.sum(allFeaturesInGroup, "=" , 1));
            } else {
                //Apply [From..To] cardinality
                addConstraint(cs4model.sum(allFeaturesInGroup, ">=" , ((IfmlCRange) ifmlCardinality).getIfmlCFrom()));
                addConstraint(cs4model.sum(allFeaturesInGroup, "<=" , ((IfmlCRange) ifmlCardinality).getIfmlCTo()));
            }
        }
    }

    /**
     * This function gets all features inside a group and stores in BoolVar array
     * @param ifmlGroupDecl IfmlGroupDecl object
     * @return a list of all features inside ifmlGroupDecl object
     */
    private BoolVar[] getAllFeaturesInGroup(IfmlGroupDecl ifmlGroupDecl) {
        ArrayList<String> featureList = ifmlGroupDecl.getFeatureNames();
        BoolVar[] boolVars = cs4model.retrieveBoolVars();
        List<BoolVar> newBoolVars = new ArrayList<BoolVar>();
        for(BoolVar bool : boolVars) {
            for(String feature : featureList){
                    if(bool.getName().equals(feature)) {
                    newBoolVars.add(bool);
                }
            }
        }
        BoolVar[] allFeaturesInGroup = new BoolVar[newBoolVars.size()];
        allFeaturesInGroup = newBoolVars.toArray(allFeaturesInGroup);
        
        return allFeaturesInGroup;
       
    }
    
    /**
     * This function takes a List<String> and removes any duplicate entries before returning the list
     * @param result a list of strings
     * @return a list with unique set of values
     */
    private List<String> removeDuplicateFromList(List<String> result) {
        HashSet<String> tempHashSet = new HashSet<String>();
        tempHashSet.addAll(result);
        result.clear();
        result.addAll(tempHashSet);
        return result;
    }
    
}