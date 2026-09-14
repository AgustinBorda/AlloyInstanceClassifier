package modelrelaxer;


import edu.mit.csail.sdg.parser.CompModule;

public class SimpleModelRelaxer implements ModelRelaxer {

    private final ModelRelaxer sigRelRelaxer;
    private final ModelRelaxer factRelaxer;
    private final ModelRelaxer funcRelaxer;

    public SimpleModelRelaxer(CompModule w) {
        sigRelRelaxer = new SignatureAndRelationRelaxer(w);
        factRelaxer = new DummyModelRelaxer();
        funcRelaxer = new DummyModelRelaxer();
    }

    @Override
    public String relaxModel() {
        return sigRelRelaxer.relaxModel() + "\n" + factRelaxer.relaxModel() + "\n" + funcRelaxer.relaxModel();
    }

    @Override
    public String getConstrains() {
        return sigRelRelaxer.getConstrains() + "\n" + factRelaxer.getConstrains() + "\n" + funcRelaxer.getConstrains();
    }
}
