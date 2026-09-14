package modelrelaxer;


import constraintgenerator.AlloyExpressionConstraintGenerator;
import constraintgenerator.ConstraintGenerator;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.parser.CompModule;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class SignatureAndRelationRelaxer implements ModelRelaxer{

    private final CompModule world;
    private ConstraintGenerator constraintGenerator;
    private List<String> constraints;

    public SignatureAndRelationRelaxer(CompModule w) {
        world = w;
        constraintGenerator = new AlloyExpressionConstraintGenerator();
        constraints = new ArrayList<>();

    }

    @Override
    public String relaxModel() {
        StringBuilder result = new StringBuilder();

        for(Sig s: world.getAllReachableUserDefinedSigs()) {
            if(!s.label.startsWith("this/"))
                continue;
            result.append(getRelaxedSig(s));
            String constraint = constraintGenerator.generateConstraint(s);
            if(!constraint.trim().isEmpty())
                constraints.add(constraint);
            for(Sig.Field f: s.getFields()) {
                result.append(getRelaxedRel(f));
                constraint = constraintGenerator.generateConstraint(f);
                if(!constraint.trim().isEmpty())
                    constraints.add(constraint);
            }
            result.append("}\n");
        }
        return result.toString();
    }

    @Override
    public String getConstrains() {
        StringBuilder result = new StringBuilder();
        for (int i = 0; i< constraints.size(); i++) {
            result.append("fact constraint_").append(i).append("{ ").append(constraints.get(i)).append("}\n");
        }
        return result.toString();
    }

    private String getRelaxedSig(Sig s) {
        StringBuilder result = new StringBuilder();
        result.append("sig").append(" ").append(clean(s.label)).append(" ");
        if (s instanceof Sig.SubsetSig) {
            String parents = ((Sig.SubsetSig) s).parents.toString();
            parents = parents.substring(1,parents.length()-1).replaceAll(", ", " + ");
            result.append("in ").append(parents);
        }
        else {
            if (!s.isTopLevel()) {
                result.append("extends ").append(((Sig.PrimSig) s).parent);
            }
        }
        result.append(" {\n");
        return result.toString();
    }

    private String getRelaxedRel(Sig.Field f) {
        StringBuilder result = new StringBuilder();
        result.append(clean(f.label)).append(": ");
        List<String> relatedSigs = mergeTypeEntries(f.type());
        for(int i = 1; i< relatedSigs.size(); i++) {
            result.append("set ").append(relatedSigs.get(i));
            if(i < relatedSigs.size()-1)
                result.append(" -> ");
        }
        result.append(",\n");
        return result.toString();
    }

    private static String clean(String s) {
        return s.replaceAll("this/","");
    }

    private static List<String> mergeTypeEntries(Type type) {
        List<String> result = new ArrayList<>();
        String clean = type.toString().substring(1,type.toString().length()-1);
        String[] entries = clean.split(", ");
        List<String[]> splitEntries = new ArrayList<>();
        for (String entry : entries) {
            splitEntries.add(entry.split("->"));
        }
        for (int i = 0; i < splitEntries.get(0).length; i++) {
            Set<String> elements = new HashSet<>();
            for (String[] entry: splitEntries) {
                elements.add(entry[i]);
            }
            StringBuilder elem = new StringBuilder();
            for (String element: elements)
                elem.append(element).append(" + ");
            elem.replace(elem.length()-3, elem.length(), "");
            result.add("(" + elem + ")");
        }
        return result;
    }

}
