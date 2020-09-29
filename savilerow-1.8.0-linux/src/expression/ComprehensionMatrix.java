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

public class ComprehensionMatrix extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    // One-dimensional matrix comprehension.
    // May be nested.
    public ComprehensionMatrix(ASTNode innerexp, ArrayList<ASTNode> generators, ASTNode conds) {
        super(innerexp, new Container(generators), conds, new IntegerDomain(new Range(NumberConstant.make(1), null)));
    }
    
    public ComprehensionMatrix(ASTNode innerexp, ArrayList<ASTNode> generators, ASTNode conds, ASTNode index) {
        super(innerexp, new Container(generators), conds, index);
    }
    
    public ASTNode copy()
    {
        return new ComprehensionMatrix(getChild(0), getChild(1).getChildren(), getChild(2), getChild(3));
    }
    public boolean toFlatten(boolean propagate) { return false; }
    
    // Does it contain bools/constraints
    public boolean isRelation() {
        return getChild(0).isRelation();
    }
    public boolean isNumerical() {
        return getChild(0).isNumerical();
    }
    
    public int getDimension() {
        return 1+getChild(0).getDimension();
    }
    
    @Override
    public boolean typecheck(SymbolTable st) {
        if(!getChild(0).typecheck(st) || !getChild(1).typecheck(st) || !getChild(2).typecheck(st) || !getChild(3).typecheck(st))
            return false;
        
        for(int i=0; i<getChild(1).numChildren(); i++) {
            ASTNode quant=getChild(1).getChild(i);
            if(getParent().getDomainForId(quant.getChild(0))!=null || st.hasVariable(quant.getChild(0).toString())) {
                CmdFlags.println("ERROR: In matrix comprehension: "+this); 
                CmdFlags.println("ERROR: Variable `"+quant.getChild(0)+"' is already defined.");
                return false;
            }
            for(int j=0; j<i; j++) {
                if(quant.getChild(0).equals(getChild(1).getChild(j).getChild(0))) {
                    // Defined to the left in the same comprehension.
                    CmdFlags.println("ERROR: In matrix comprehension: "+this); 
                    CmdFlags.println("ERROR: Variable `"+quant.getChild(0)+"' is already defined.");
                    return false;
                }
            }
        }
        
        if(getChild(2).getCategory()>ASTNode.Quantifier) {
            System.out.println("ERROR: In matrix comprehension: "+this); 
            System.out.println("ERROR: Decision variable in condition.");
            return false;
        }
        if(! getChild(2).isRelation()) {
            System.out.println("ERROR: In matrix comprehension: "+this); 
            System.out.println("ERROR: The condition is not a boolean expression.");
            return false;
        }
        if(getChild(3).getCategory()>ASTNode.Quantifier) {
            System.out.println("ERROR: In matrix comprehension: "+this); 
            System.out.println("ERROR: Decision variable in index domain.");
            return false;
        }
        if(! getChild(3).isSet()) {
            System.out.println("ERROR: In matrix comprehension: "+this); 
            System.out.println("ERROR: Index domain is not a set.");
            return false;
        }
        return true;
    }
    
    public ASTNode simplify() {
        //  Catch some common cases of inefficiently written comprehensions.
        
        //  No variables and 'true' condition.
        if(getChild(1).numChildren()==0 && getChild(2).isConstant() && getChild(2).getValue()==1) {
            // Check the index domain is constant.
            if(getChild(3).getCategory()==ASTNode.Constant) {
                //  Fiddle the upper bound onto the index domain. Length of the list is 1, so index domain is just int(lb..lb)
                ArrayList<Intpair> intervals=getChild(3).getIntervalSet();
                ASTNode idxdom=new IntegerDomain(new Range(NumberConstant.make(intervals.get(0).lower), NumberConstant.make(intervals.get(0).lower)));
                
                ASTNode cm=CompoundMatrix.make(idxdom, list(getChild(0)), getChild(0).isRelation());
                //System.out.println("Replacing: "+this+" with: "+cm);
                return cm;
            }
        }
        
        //  Lift parameter expressions from the inner expression into the condition.
        if(getParent()!=null && getParent() instanceof OrVector) {
            if(getChild(0) instanceof And) {
                for(int i=0; i<getChild(0).numChildren(); i++) {
                    if(getChild(0).getChild(i).getCategory()<=ASTNode.Quantifier) {
                        ArrayList<ASTNode> inner=getChild(0).getChildren();
                        ASTNode lift=inner.remove(i);
                        ASTNode cm=new ComprehensionMatrix(new And(inner), getChild(1).getChildren(), new And(lift, getChild(2)), getChild(3));
                        //System.out.println("Replacing: "+this+" with: "+cm);
                        return cm;
                    }
                }
            }
        }
        
        //  Check for equalities in the condition.
        if(getChild(2) instanceof Equals) {
            ASTNode generators=getChild(1);
            for(int i=0; i<generators.numChildren(); i++) {
                Pair<ASTNode, ASTNode> p=checkEquality(getChild(2), generators.getChild(i), i);
                if(p!=null) {
                    //  Remove the generator, and substitute p.second in for the comprehension variable.  
                    //  Replace the equality condition with p.first.
                    ArrayList<ASTNode> newq=getChild(1).getChildren();
                    newq.remove(i);
                    
                    ASTNode cm=new ComprehensionMatrix(getChild(0), newq, p.getFirst(), getChild(3));
                    ReplaceASTNode r=new ReplaceASTNode(generators.getChild(i).getChild(0), p.getSecond());
                    cm=r.transform(cm);
                    
                    //System.out.println("Replacing: "+this+" with: "+cm);
                    
                    return cm;
                }
            }
        }
        
        if(getChild(2) instanceof And) {
            for(int i=0; i<getChild(2).numChildren(); i++) {
                if(getChild(2).getChild(i) instanceof Equals) {
                    // Loop over the generators.
                    ASTNode generators=getChild(1);
                    for(int j=0; j<generators.numChildren(); j++) {
                        Pair<ASTNode, ASTNode> p=checkEquality(getChild(2).getChild(i), generators.getChild(j), j);
                        if(p!=null) {
                            //  Remove the generator, and substitute p.second in for the comprehension variable.  
                            //  Replace the equality condition with p.first.
                            ArrayList<ASTNode> newq=getChild(1).getChildren();
                            newq.remove(j);
                            
                            ArrayList<ASTNode> conditions=getChild(2).getChildren();
                            conditions.set(i, p.getFirst());
                            
                            ASTNode cm=new ComprehensionMatrix(getChild(0), newq, new And(conditions), getChild(3));
                            ReplaceASTNode r=new ReplaceASTNode(generators.getChild(j).getChild(0), p.getSecond());
                            cm=r.transform(cm);
                            
                            //System.out.println("Replacing: "+this+" with: "+cm);
                            
                            return cm;
                        }
                    }
                }
            }
        }
        
        return null;
    }
    
    //  Takes an equality (condition) and a (q : domain), and returns a replacement condition and the replacement for q.
    private Pair<ASTNode, ASTNode> checkEquality(ASTNode eq, ASTNode q, int index) {
        Pair<ASTNode, ASTNode> p=checkEquality(eq.getChild(0), eq.getChild(1), q, index);
        if(p != null) {
            return p;
        }
        else {
            return checkEquality(eq.getChild(1), eq.getChild(0), q, index);
        }
    }
    
    private Pair<ASTNode, ASTNode> checkEquality(ASTNode x1, ASTNode x2, ASTNode q, int index) {
        ASTNode var=q.getChild(0);
        if(x1.equals(var)) {
            if(x2.isConstant()) {
                return new Pair<ASTNode, ASTNode>(new InSet(x2, q.getChild(1)), x2);
            }
            if(x2 instanceof Identifier) {
                //  This can be generalised to deal with expressions. 
                //  Check if x2 is defined after var. If so, can't replace var with x2.  Instead x2 will be replaced with var. 
                for(int i=index+1; i<getChild(1).numChildren(); i++) {
                    if(getChild(1).getChild(i).getChild(0).equals(x2)) {
                        return null;
                    }
                }
                return new Pair<ASTNode, ASTNode>(new InSet(x2, q.getChild(1)), x2);
            }
        }
        return null;
    }
    
    @Override
    public ASTNode getDomainForId(ASTNode id) {
        for(int i=0; i<getChild(1).numChildren(); i++) {
            ASTNode quant=getChild(1).getChild(i);
            if(quant.getChild(0).equals(id)) {
                return quant.getChild(1);
            }
        }
        return getParent().getDomainForId(id);
    }
    
    public Intpair getBounds() {
        return getChild(0).getBounds();  // The bounds of the inner expression will contain all the elements of the concrete matrix.
    }
    public PairASTNode getBoundsAST() {
        return getChild(0).getBoundsAST();
    }
    
    // Should never need to be output in the instance-level formats. Just Dominion and E'
    
    public void toDominionInner(StringBuilder b, boolean bool_context) {
        b.append("[");
        getChild(0).toDominion(b, false);
        b.append("|");
        
        // Quantifiers
        for(int i=0; i<getChild(1).numChildren(); i++)
        {
            getChild(1).getChild(i).toDominionParam(b);
            b.append(", ");
        }
        
        // Conditions
        getChild(2).toDominionParam(b);  // should be true if there are no conditions.
        b.append("]");
    }
    public void toDominionParam(StringBuilder b){
        b.append("[");
        getChild(0).toDominionParam(b);
        b.append("|");
        
        // Quantifiers
        for(int i=0; i<getChild(1).numChildren(); i++)
        {
            getChild(1).getChild(i).toDominionParam(b);
            b.append(", ");
        }
        
        // Conditions
        getChild(2).toDominionParam(b);  // should be true if there are no conditions.
        b.append("]");
    }
    
    public String toString() {
        StringBuilder st=new StringBuilder();
        st.append("[");
        st.append(getChild(0));
        st.append("|");
        for(int i=0; i<getChild(1).numChildren(); i++) {
            st.append(getChild(1).getChild(i).toString());
            st.append(", ");
        }
        st.append(getChild(2));
        st.append(" ;");
        st.append(getChild(3));
        st.append("]");
        return st.toString();
    }
}
