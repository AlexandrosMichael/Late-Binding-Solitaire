package savilerow;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2020 Peter Nightingale
    
    This file is part of Savile Row.
    
    Savile Row is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.
    
    Savile Row is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.
    
    You should have received a copy of the GNU General Public License
    along with Savile Row.  If not, see <http://www.gnu.org/licenses/>.

*/

import java.util.*;

// Remove variables that are equal to a linear mapping of another variable.

public class TransformDeleteFuncVars extends TreeTransformerBottomUpNoWrapper
{
    public TransformDeleteFuncVars(Model mod) {
        super(mod);
    }
    
    protected NodeReplacement processNode(ASTNode curnode)
    {
        //  Only deal with equalities in the top-level And, so that the top
        //  And is replaced and all other constraints are processed again. 
        if(curnode instanceof Equals && curnode.getParent()!=null 
            && ( (curnode.getParent() instanceof And && curnode.getParent().getParent() instanceof Top)
                || curnode.getParent() instanceof Top)) {
            
            ASTNode c0=curnode.getChild(0);
            ASTNode c1=curnode.getChild(1);
            
            if(c0 instanceof Identifier && c1 instanceof WeightedSum) {
                //  Need to check only one decision variable in c1
                if(linearOneVar(c1)) {
                    //  Check if decision variable has all values that sum can take. 
                    ArrayList<Intpair> diff=Intpair.setDifference(c1.getIntervalSetExp(), c0.getIntervalSetExp());
                    if(Intpair.numValues(diff)==0) {
                        m.global_symbols.unifyVariablesLinear(c0, c1);
                        return new NodeReplacement(new BooleanConstant(true));
                    }
                }
            }
            
            if(c1 instanceof Identifier && c0 instanceof WeightedSum) {
                //  Need to check only one decision variable in c0
                if(linearOneVar(c0)) {
                    //  Check if decision variable has all values that sum can take. 
                    ArrayList<Intpair> diff=Intpair.setDifference(c0.getIntervalSetExp(), c1.getIntervalSetExp());
                    if(Intpair.numValues(diff)==0) {
                        m.global_symbols.unifyVariablesLinear(c1, c0);
                        return new NodeReplacement(new BooleanConstant(true));
                    }
                }
                m.global_symbols.unifyVariablesLinear(c1, c0);
                return new NodeReplacement(new BooleanConstant(true));
            }
        }
        return null;
    }
    
    //  Is the sum a simple linear function of one variable?
    private boolean linearOneVar(ASTNode ws) {
        int decvars=0;
        for(int i=0; i<ws.numChildren(); i++) {
            if(ws.getChild(i) instanceof Identifier && ws.getChild(i).getCategory()==ASTNode.Decision) {
                decvars++;
            }
            else if(!ws.getChild(i).isConstant()) {
                //  Something other than a constant or decision variable. 
                return false;
            }
        }
        return decvars==1;
    }
}
