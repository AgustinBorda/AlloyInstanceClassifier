package constraintgenerator;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.*;

import java.util.*;

public class AlloyExpressionConstraintGenerator implements ConstraintGenerator {

    private static final String sigName = "s";
    private static final String relName = "r";

    @Override
    public String generateConstraint(Sig s) {
        String value = "";
        if(s.isOne != null)
            value = "one " + s.label;
        if(s.isSome != null)
            value = "some " + s.label;
        if(s.isLone != null)
            value = "lone " + s.label;
        return value;
    }


    @Override
    public String generateConstraint(Pair<String, Expr> fact) {
        return fact.b.toString();
    }

    @Override
    public String generateConstraint(Func f) {
        return f.getBody().toString();
    }

    @Override
    public String generateConstraint(Sig.Field f) {
        StringBuilder result = new StringBuilder();
        List<String> variables = new ArrayList<>();

        variables.add(sigName);
        result.append("all ").append(sigName).append(":").append(clean(f.sig.label)).append(" | ");

        String[] relatedSigs = f.type().toString().substring(1,f.type().toString().length()-1).split("->");
        for(int i = 1; i< relatedSigs.length; i++) {
            variables.add(relName + i);
            result.append("all ").append(variables.get(i)).append(": ").append(clean(relatedSigs[i] + " | "));
        }

        Set<String> constraints = generateConstraints(f.decl().expr, variables, clean(f.label),1);
        if(!constraints.isEmpty()) {
            Iterator<String> constraintIterator = constraints.iterator();

            while (constraintIterator.hasNext()) {
                result.append(constraintIterator.next());
                if (constraintIterator.hasNext()) {
                    result.append(" and ");
                }
            }
        }
        else {
            result = new StringBuilder();
        }

        return result.toString();
    }

    /**
     * The expressions are a UnaryExpr (binary relations) or a Binary tree of BinaryExpr where the left son
     * is a Unary Expr and the right son is the rest of the expression. If we have a complex expression starting
     * with a constraint, it also will be a UnaryExpr, but we can ignore it, as the only restriction allowed is set, so it
     * can be ignored.
     * this always starts with the first constraint.
     */
    private Set<String> generateConstraints(Expr expression, List<String> variables, String name, int position) {
        Set<String> result = new HashSet<>();
        if(expression instanceof ExprUnary) {
            ExprUnary expr = (ExprUnary) expression;
            if(expr.sub instanceof ExprBinary)
                result.addAll(generateConstraints(expr.sub, variables, name, position));
            result.addAll(generateUnaryConstraints(expr, variables, name, position));
        }
        else {
            ExprBinary exprBinary = (ExprBinary) expression;
            if(exprBinary.right instanceof ExprBinary)
                result.addAll(generateConstraints(exprBinary.right, variables, name, position+1));
            result.addAll(generateBinaryConstraints(exprBinary, variables, name, position));
        }
        return result;
    }


    private Set<String> generateUnaryConstraints(ExprUnary exprUnary, List<String> variables, String name, int position) {
        Set<String> result = new HashSet<>();
        StringBuilder join = new StringBuilder();

        join.append(variables.get(0)).append(".").append(name);

        for(int j = position; j > 1; j--) {
            join = new StringBuilder(variables.get(j) + ".(" + join + ")");
        }

        if(exprUnary.op == ExprUnary.Op.ONEOF)
            result.add(" one " + join);
        if(exprUnary.op == ExprUnary.Op.LONEOF)
            result.add(" lone " + join);
        if(exprUnary.op == ExprUnary.Op.SOMEOF)
            result.add(" some " + join);

        return result;
    }

    private Set<String> generateBinaryConstraints(ExprBinary exprBinary, List<String> variables, String name, int position) {
        Set<String> result = new HashSet<>();
        StringBuilder join = new StringBuilder();
        StringBuilder joinAfter = new StringBuilder();

        join.append(variables.get(0)).append(".").append(name);
        joinAfter.append(variables.get(0)).append(".").append(name);

        for(int j = variables.size()-1 ; j > position; j--) {
            join.append(".").append(variables.get(j));
        }
        for(int j = position; j > 0; j--) {
            joinAfter = new StringBuilder(variables.get(j) + ".(" + joinAfter + ")");
        }

        if(exprBinary.op == ExprBinary.Op.ANY_ARROW_LONE) {
            result.add(" lone " + joinAfter);
        }
        if(exprBinary.op == ExprBinary.Op.ANY_ARROW_ONE) {
            result.add(" one " + joinAfter);
        }
        if(exprBinary.op == ExprBinary.Op.ANY_ARROW_SOME) {
            result.add(" some " + joinAfter);
        }
        if(exprBinary.op == ExprBinary.Op.LONE_ARROW_ANY) {
            result.add(" lone " + join);
        }
        if(exprBinary.op == ExprBinary.Op.LONE_ARROW_LONE) {
            result.add(" lone " + join);
            result.add(" lone " + joinAfter);
        }
        if(exprBinary.op == ExprBinary.Op.LONE_ARROW_ONE) {
            result.add(" lone " + join);
            result.add(" one " + joinAfter);
        }
        if(exprBinary.op == ExprBinary.Op.LONE_ARROW_SOME) {
            result.add(" lone " + join);
            result.add(" some " + joinAfter);
        }
        if(exprBinary.op == ExprBinary.Op.SOME_ARROW_ANY) {
            result.add(" some " + join);
        }
        if(exprBinary.op == ExprBinary.Op.SOME_ARROW_LONE) {
            result.add(" some " + join);
            result.add(" lone " + joinAfter);
        }
        if(exprBinary.op == ExprBinary.Op.SOME_ARROW_ONE) {
            result.add(" some " + join);
            result.add(" one " + joinAfter);
        }
        if(exprBinary.op == ExprBinary.Op.SOME_ARROW_SOME) {
            result.add(" some " + join);
            result.add(" some " + joinAfter);
        }
        if(exprBinary.op == ExprBinary.Op.ONE_ARROW_ANY) {
            result.add(" one " + join);
        }
        if(exprBinary.op == ExprBinary.Op.ONE_ARROW_LONE) {
            result.add(" one " + join);
            result.add(" lone " + joinAfter);
        }
        if(exprBinary.op == ExprBinary.Op.ONE_ARROW_ONE) {
            result.add(" one " + join);
            result.add(" one " + joinAfter);
        }
        if(exprBinary.op == ExprBinary.Op.ONE_ARROW_SOME) {
            result.add(" one " + join);
            result.add(" some " + joinAfter);
        }

        return result;
    }

    private static String clean(String s) {
        return s.replaceAll("this/","");
    }
}
