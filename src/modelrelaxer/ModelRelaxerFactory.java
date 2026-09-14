package modelrelaxer;


import edu.mit.csail.sdg.parser.CompModule;

public class ModelRelaxerFactory {

    public ModelRelaxer createModelRelaxer(CompModule w) {
        return new SimpleModelRelaxer(w);
    }

}
