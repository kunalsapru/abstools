/**
 * Copyright (c) 2009-2011, The HATS Consortium. All rights reserved. 
 * This file is licensed under the terms of the Modified BSD License.
 */
package abs.frontend.ifml;

import org.chocosolver.solver.Model;
import org.chocosolver.solver.variables.IntVar;

/**
* Trivial example showing how to use Choco Solver
* to solve the equation system
* x + y < 5
* x * y = 4
* with x in [0,5] and y in {2, 3, 8}
*
* @author Charles Prud'homme, Jean-Guillaume Fages
* @since 9/02/2016
*/

public class ChocoSolver {
    
    public static void main(String[] args){
        //1.Create Model
        Model model = new Model("My First Choco Model");
        //2.Create Variables
        IntVar x = model.intVar("X", 0, 5);
        IntVar y = model.intVar("Y", new int[]{2,3,8,-2});
        //3. Post constraints
        model.arithm(x,"+",y,"<",5).post();
        model.times(x,y,4).post();
        //4.Solve the problem
        model.getSolver().solve();
        //5.Print the solution
        System.out.println(x+" and "+y);
    }

}
