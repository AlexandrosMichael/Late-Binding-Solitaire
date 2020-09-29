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

//   Convert sum constraints to AMOPBs. 

public class TransformSumToAMOPB extends TreeTransformerBottomUp
{
    public TransformSumToAMOPB(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
    {
        //  Avoid non-top-level cts, which will fall back to the tree encoding. 
        if(curnode.getParent()!=null && !curnode.getParent().inTopAnd()) {
            return null;
        }
        
        ArrayList<ASTNode> ch=null;
        ArrayList<Long> wts=null;
        long cmp=0L;
        long encoding=0L;
        
        //  Catch all cases of a sum in a binop.
        if(curnode instanceof ToVariable && curnode.getChild(0) instanceof WeightedSum && curnode.getChild(1).isConstant()) {
            ch=curnode.getChild(0).getChildren();
            wts=((WeightedSum)curnode.getChild(0)).getWeights();
            
            cmp=curnode.getChild(1).getValue();
        }
        
        if(curnode instanceof Less && curnode.getChild(0) instanceof WeightedSum && curnode.getChild(1).isConstant()) {
            ch=curnode.getChild(0).getChildren();
            wts=((WeightedSum)curnode.getChild(0)).getWeights();
            
            cmp=curnode.getChild(1).getValue()-1;  // convert to <=
        }
        
        if(curnode instanceof LessEqual && curnode.getChild(0) instanceof WeightedSum && curnode.getChild(1).isConstant()) {
            ch=curnode.getChild(0).getChildren();
            wts=((WeightedSum)curnode.getChild(0)).getWeights();
            
            cmp=curnode.getChild(1).getValue();
        }
        
        if(curnode instanceof Less && curnode.getChild(1) instanceof WeightedSum && curnode.getChild(0).isConstant()) {
            // k < sum  becomes  -sum < -k  becomes  -sum <= -k-1
            ch=curnode.getChild(1).getChildren();
            wts=((WeightedSum)curnode.getChild(1)).getWeights();
            for(int i=0; i<wts.size(); i++) {
                wts.set(i, -wts.get(i));  // negate the weights
            }
            
            cmp=-curnode.getChild(0).getValue()-1;
        }
        
        if(curnode instanceof LessEqual && curnode.getChild(1) instanceof WeightedSum && curnode.getChild(0).isConstant()) {
            // k <= sum  becomes  -sum <= -k 
            ch=curnode.getChild(1).getChildren();
            wts=((WeightedSum)curnode.getChild(1)).getWeights();
            for(int i=0; i<wts.size(); i++) {
                wts.set(i, -wts.get(i));  // negate the weights
            }
            
            cmp=-curnode.getChild(0).getValue();
        }
        
        if(ch!=null) {
            //  Is it entirely boolean
            boolean allBool=true;
            for(int i=0; i<ch.size(); i++) {
                if(!ch.get(i).isRelation()) {
                    allBool=false;
                    break;
                }
            }
            
            //  Check command-line flags.
            if((allBool && !(CmdFlags.getSatPBMDD() || CmdFlags.getSatPBGPW() || CmdFlags.getSatPBSWC() || CmdFlags.getSatPBGGT())) 
                || (!allBool && !(CmdFlags.getSatSumMDD() || CmdFlags.getSatSumGPW() || CmdFlags.getSatSumSWC() || CmdFlags.getSatSumGGT()))) {
                return null;
            }
            
            if(allBool) {
                encoding=CmdFlags.getSatPBMDD() ? 1 : (CmdFlags.getSatPBGPW()? 2 : (CmdFlags.getSatPBSWC()? 3 : 4));
            }
            else {
                encoding=CmdFlags.getSatSumMDD() ? 1 : (CmdFlags.getSatSumGPW()? 2 : (CmdFlags.getSatSumSWC()? 3 : 4));
            }
            
            //  Flip any negative weights of non-boolean variables.
            // Shift any terms that go below 0 -- non-bool expressions only -- guaranteed by lower bound <0. 
            for(int i=0; i<ch.size(); i++) {
                if(! (ch.get(i).isConstant())) {
                    Intpair bnds=ch.get(i).getBounds();
                    if((bnds.lower<0 || bnds.upper>1) && wts.get(i)<0) {
                        wts.set(i, -wts.get(i));
                        ch.set(i, new MultiplyMapper(ch.get(i), NumberConstant.make(-1)));
                    }
                    if(bnds.lower<0) {
                        ch.set(i, new ShiftMapper(ch.get(i), NumberConstant.make(-bnds.lower)));
                        cmp=cmp+(-bnds.lower)*wts.get(i);
                    }
                }
            }
            
            //  If it's an equality, break it up into inequalities. 
            //  Then recursive calls to do the transformation. 
            if(curnode instanceof ToVariable) {
                ASTNode c1=new LessEqual(curnode.getChild(0), curnode.getChild(1)); 
                ASTNode c2=new LessEqual(curnode.getChild(1), curnode.getChild(0));
                
                NodeReplacement nr1=processNode(c1);
                NodeReplacement nr2=processNode(c2);
                
                return new NodeReplacement(new And(nr1.current_node, nr2.current_node), null, new And(nr1.new_constraint, nr2.new_constraint));
            }
            
            //  Parameters of the AMOPB constraint.
            ArrayList<ASTNode> amoproducts=new ArrayList<ASTNode>();
            
            for(int i=0; i<ch.size(); i++) {
                if(ch.get(i)==null) {
                    continue;   //  This element has been deleted
                }
                
                if(ch.get(i).isConstant()) {
                    long val=ch.get(i).getValue()*wts.get(i);
                    cmp -= val;  //  Move to the other side of the <=.
                }
                else {
                    ArrayList<ASTNode> coeffs_onevar=new ArrayList<ASTNode>();
                    ArrayList<ASTNode> bools_onevar=new ArrayList<ASTNode>();
                    
                    if(wts.get(i)>0) {
                        ArrayList<Intpair> dom=ch.get(i).getIntervalSetExp();
                        long coeff=wts.get(i);
                        // chop the smallest value. 
                        long smallestval=dom.get(0).lower;
                        
                        for(int j=0; j<dom.size(); j++) {
                            for(long k=dom.get(j).lower; k<=dom.get(j).upper; k++) {
                                if(k!=smallestval) {
                                    coeffs_onevar.add( NumberConstant.make((coeff*k)-(coeff*smallestval)));
                                    if(ch.get(i).isRelation() && k==1) {
                                        bools_onevar.add(ch.get(i));   /// Simplify the expression for boolean variables. 
                                    }
                                    else {
                                        bools_onevar.add(new Equals(ch.get(i), NumberConstant.make(k)));
                                    }
                                }
                            }
                        }
                        
                        //  Adjust the other side of the binop to subtract the smallest val. 
                        cmp -= smallestval*coeff;
                    }
                    else {
                        // Should be boolean if there is a negative coeff. 
                        Intpair bnds=ch.get(i).getBounds();
                        assert bnds.lower>=0 && bnds.upper<=1;
                        
                        long coeff=wts.get(i);
                        cmp+=(-coeff);
                        
                        coeffs_onevar.add(NumberConstant.make(-coeff));
                        if(ch.get(i).isRelation()) {
                            bools_onevar.add(new Negate(ch.get(i)));
                        }
                        else {
                            bools_onevar.add(new Equals(ch.get(i), NumberConstant.make(0)));
                        }
                    }
                    
                    amoproducts.add(CompoundMatrix.make(CompoundMatrix.make(coeffs_onevar), CompoundMatrix.make(bools_onevar)));
                }
            }
            
            
            AMOPB amo=new AMOPB(CompoundMatrix.make(amoproducts), NumberConstant.make(cmp), NumberConstant.make(encoding));
            
            ASTNode cts=amo.collectAMOGroups(m);
            
            return new NodeReplacement(amo, null, cts);
        }
        
	    return null;
    }
}

