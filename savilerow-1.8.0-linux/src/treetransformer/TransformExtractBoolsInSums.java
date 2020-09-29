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

// Flatten any boolean expressions (such as x=a for some integer variable x and value a) contained in a sum.
// This is to enable AMO groups. 

public class TransformExtractBoolsInSums extends TreeTransformerBottomUp
{
    boolean propagate;
    public TransformExtractBoolsInSums(Model mod)
    {
        super(mod);
        cache=new HashMap<ASTNode, ASTNode>();
        inverseCache=new HashMap<ASTNode, ASTNode>();
    }
    
    HashMap<ASTNode, ASTNode> cache;
    public static HashMap<ASTNode, ASTNode> inverseCache;
    
    protected NodeReplacement processNode(ASTNode curnode) {
        if(curnode.isRelation() && (curnode.getParent() instanceof WeightedSum) 
            && !(curnode instanceof Identifier) 
            && !(curnode instanceof Negate && curnode.getChild(0) instanceof Identifier))
        {
            if(cache.containsKey(curnode)) {
                //System.out.println("replacing: "+curnode+" with cached: "+cache.get(curnode));
                return new NodeReplacement(cache.get(curnode), null, null);  //  Reuse aux var. 
            }
            else {
                ASTNode auxvar=m.global_symbols.newAuxHelper(curnode);
                ASTNode flatcon=new ToVariable(curnode, auxvar);
                m.global_symbols.auxVarRepresentsConstraint(auxvar.toString(), curnode.toString());
                cache.put(curnode, auxvar);
                inverseCache.put(auxvar, curnode);
                //System.out.println("replacing: "+curnode+" with new: "+auxvar);
                return new NodeReplacement(auxvar, null, flatcon);
            }
        }
        return null;
    }
}
