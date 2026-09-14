package alloyRunner;


import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class SimpleAlloyRunner implements AlloyRunner {

    private A4Options opt;

    public SimpleAlloyRunner(){
        opt = new A4Options();
        opt.solver = A4Options.SatSolver.SAT4J;
        opt.noOverflow = true;
    }

    @Override
    public int runModelAndReturnInstanceQuantity(String model) {
        CompModule world = CompUtil.parseEverything_fromString(A4Reporter.NOP, model);
        int instances = 0;
        for (Command c : world.getAllCommands()) {
            if (c.label.equals("overspecification") || c.label.equals("underspecification") || c.label.equals("error")) {
                A4Solution sol = TranslateAlloyToKodkod.execute_command(A4Reporter.NOP, world.getAllReachableSigs(), c, opt);
                while (sol.satisfiable() && instances < 10000) {
                    instances++;
                    sol = sol.next();
                }
            }
        }
        return instances;
    }
}
