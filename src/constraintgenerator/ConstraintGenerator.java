package constraintgenerator;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;

public interface ConstraintGenerator {

    String generateConstraint(Sig s);

    String generateConstraint(Sig.Field f);

    String generateConstraint(Pair<String, Expr> fact);

    String generateConstraint(Func f);

}
