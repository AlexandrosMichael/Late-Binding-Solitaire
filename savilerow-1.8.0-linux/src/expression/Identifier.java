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
import java.io.*;

public class Identifier extends ASTNode {
    public static final long serialVersionUID = 1L;
    protected transient Model m;
    private String name;
    
    public Identifier(Model _m, String id) {
        super();
        name = id;
        m=_m;
    }
    
    public boolean hasModel() {
        return true;
    }
    public Model getModel() {
        return m;
    }
    public void setModel(Model _m) {
        m=_m;
    }
    
    public String toString() {
        return name;
    }

    public ASTNode copy() {
        return new Identifier(m, name);
    }

    public String getName() {
        return name;
    }
    
    //  equals and hashCode ignore the model pointer.
    @Override
    public boolean equals(Object other) {
        if (! (other instanceof Identifier)) {
            return false;
        }
        return ((Identifier) other).name.equals(name);
    }
    
    @Override
    public int hashCode() {
        return name.hashCode();
    }
    
    // Is it a bool or matrix of bool.
    public boolean isRelation() {
        ASTNode dom=getDomain();
        
        if (dom.isBooleanSet()) {
            return true;
        }
        if (dom instanceof MatrixDomain && dom.getChild(0).isBooleanSet()) {
            return true;
        }
        return false;
    }
    public boolean strongProp() {
        return true;    //  Either stands for a matrix of constants or a single decision variable at this point. 
    }
    public boolean isNumerical() {
        return !this.isRelation() && !this.isSet();
    }
    public boolean isSet() {
        // An identifier may be a set if there is a letting defining it as such.
        ArrayList<ASTNode> letgivs = new ArrayList<ASTNode>(m.global_symbols.lettings_givens);
        for (int i =0; i < letgivs.size(); i++) {
            if (letgivs.get(i) instanceof Letting) {
                if (letgivs.get(i).getChild(0).equals(this)) {
                    if (letgivs.get(i).getChild(1).isSet()) {
                        return true;
                    }
                }
            }
        }
        return false;
    }
    
    public int getCategory() {
        if (m.global_symbols.hasVariable(name)) {
            return m.global_symbols.getCategory(name);
        }
        
        // Go up tree to find quantifier.
        if (this.getDomainForId(this) != null) {
            return ASTNode.Quantifier;
        }
        
        return ASTNode.Undeclared;
    }
    
    public boolean isAuxiliary() {
        return m.global_symbols.isAuxiliary(name);
    }
    
    public ASTNode getCM() {
        if(getCategory()==ASTNode.Constant) {
            return m.cmstore.getConstantMatrix(name);
        }
        else {
            return this;
        }
    }
    
    public int getDimension() {
        ASTNode dom = this.getDomainForId(this);
        if (dom == null) {
            dom = m.global_symbols.getDomain(name);
        }

        if (dom instanceof MatrixDomain) {
            return dom.numChildren() - 3;
        }
        
        return 0;
    }
    
    // For indexable expressions, return the domain of each dimension.
    public ArrayList<ASTNode> getIndexDomains() {
        if (getDimension() == 0) {
            return null;
        }
        ASTNode dom = this.getDomainForId(this);
        if (dom == null) {
            dom = m.global_symbols.getDomain(name);
        }

        if (dom instanceof MatrixDomain) {
            ArrayList<ASTNode> idxdoms = dom.getChildren(3);  //  Return only the index domains of the matrix domain.
            return idxdoms;
        }
        assert false;        // Should have found a matrixdomain.
        return null;
    }
    
    @Override
    public boolean typecheck(SymbolTable st) {
        // Checks if the identifier is defined.
        // Unfortunately shares a lot of code with method above.
        assert st.m == m;        // If this isn't true, we have two models floating around. Very strange.
        
        boolean inST=m.global_symbols.hasVariable(name);
        boolean inQ=this.getDomainForId(this)!=null;
        if(!inST && !inQ) {
            CmdFlags.println("ERROR: Identifier not defined: " + this);
            return false;
        }
        return true;
    }
    @Override
    public ASTNode simplify() {
        ASTNode rep = m.global_symbols.replacements.get(this);        // Has this symbol been replaced?
        if (rep != null) {
            return rep.copy();
        }
        
        return null;
    }
    
    // Get the full domain for this identifier.
    public ASTNode getDomain() {
        ASTNode d = m.global_symbols.getDomain(name);
        if(d==null) {
            d=this.getDomainForId(this);
        }
        assert d!=null;
        return d;
    }
    public ArrayList<Intpair> getIntervalSetExp() {
        ASTNode d=getDomain();
        if(d instanceof MatrixDomain) {
            d=d.getChild(0);
        }
        // Can do better when id refers to constant matrix. This just retrieves bounds from its matrix domain.
        return d.getIntervalSet();
    }
    
    public Intpair getBounds() {
        ASTNode d = getDomain();
        if (d instanceof MatrixDomain) {
            d = d.getChild(0);
        }
        return d.getBounds();
    }
    
    // Returns a parameter expression. If this is a quantifier id,
    public PairASTNode getBoundsAST() {
        // Also needs to check for quantifiers
        int cat = this.getCategory();

        if (cat == ASTNode.Undeclared) {
            System.out.println(this);
        }
        assert cat != ASTNode.Undeclared;

        if (cat == ASTNode.Parameter || cat == ASTNode.Constant) {
            // If this is parameter p, then its bounds are p..p
            ASTNode dom = m.global_symbols.getDomain(name);
            if (dom instanceof SimpleDomain) {
                return new PairASTNode(this, this);
            } else if (dom instanceof MatrixDomain) {
                return dom.getChild(0).getBoundsAST();
            } else {
                System.out.println("Strange parameter type in Identifier.java");
                assert false;
                return new PairASTNode(this, this);
            }
        }
        if (cat == ASTNode.Quantifier) {
            ASTNode d = this.getDomainForId(this);

            assert d != null;
            if (d instanceof MatrixDomain) {
                d = d.getChild(0);
            }

            PairASTNode p = d.getBoundsAST();

            // p may still contain some other quantifier id.

            while (p.e1.getCategory() > ASTNode.Parameter) {
                p.e1 = p.e1.getBoundsAST().e1;
            }


            while (p.e2.getCategory() > ASTNode.Parameter) {
                p.e2 = p.e2.getBoundsAST().e2;
            }


            return p;
        }

        assert cat == ASTNode.Decision;
        // If it's a decision variable, the bounds come from the domain.
        ASTNode d = m.global_symbols.getDomain(name);
        if (d instanceof MatrixDomain) {
            d = d.getChild(0);
        }
        return d.getBoundsAST();
    }
    
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        if (bool_context) {
            // Write a constraint
            if (CmdFlags.getUseBoundVars() && this.exceedsBoundThreshold()) {
                b.append("eq(");
            } else {
                b.append("w-literal(");
            }
            b.append(name);
            b.append(",1)");
        } else {
            b.append(name);
        }
    }
    
    public void toDominionInner(StringBuilder b, boolean bool_context) {
        if (bool_context) {
            // Print out a constraint
            b.append(CmdFlags.getCtName() + " ");
            b.append("literal(");
            b.append(name);
            b.append(",1)");
        } else {
            // Just the name
            b.append(name);
        }
    }
    public void toDominionParam(StringBuilder b) {
        b.append(name);
    }
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        ASTNode dom=m.global_symbols.getDomain(name);
        if (m.global_symbols.hasVariable(name) && (dom.isBooleanSet() || (dom.isIntegerSet() && dom.getBounds().equals(new Intpair(0,1))))) {
            if (bool_context) {
                b.append(name + "_BOOL");
            }
            else {
                b.append(name + "_INTEGER");
            }
        }
        else {
            b.append(name);
        }
    }
    
    public void toMinizinc(StringBuilder b, boolean bool_context) {
        ASTNode dom=m.global_symbols.getDomain(name);
        if (m.global_symbols.hasVariable(name) && (dom.isBooleanSet() || (dom.isIntegerSet() && dom.getBounds().equals(new Intpair(0,1))))) {
            if (bool_context) {
                b.append(name + "_BOOL");
            } else {
                b.append(name + "_INTEGER");
            }
        } else {
            b.append(name);
        }
    }
    
    public long directEncode(Sat satModel, long value) {
        return satModel.getDirectVariable(name, value);
    }
    public long orderEncode(Sat satModel, long value) {
        return satModel.getOrderVariable(name, value);
    }
    
    public Long toSATLiteral(Sat satModel) {
        if(isRelation()) {
            return satModel.getDirectVariable(name, 1);
        }
        else return null;
    }
    public void toSATWithAuxVar(Sat satModel, long auxVarValue) throws IOException
    {
        long identifierValue=satModel.getDirectVariable(name, 1);
        
        satModel.addClause(-auxVarValue, identifierValue);
        satModel.addClause(auxVarValue, -identifierValue);
    }
    
    public void toJSON(StringBuilder bf) {
        //   Just the name with a $ in front. 
        bf.append("\"$" + name + "\"\n");
    }
}
