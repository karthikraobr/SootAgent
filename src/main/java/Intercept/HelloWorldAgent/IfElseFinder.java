package Intercept.HelloWorldAgent;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import soot.Body;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.IfStmt;
import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.scalar.ForwardFlowAnalysis;

public class IfElseFinder extends ForwardFlowAnalysis<Unit, Set<FlowAbstraction>> {
	private final SootMethod method;

	public IfElseFinder(Body b) {
		super(new ExceptionalUnitGraph(b));
		this.method = b.getMethod();
	}

	@Override
	protected void flowThrough(Set<FlowAbstraction> in, Unit d, Set<FlowAbstraction> out) {
		List<Unit> preds = graph.getPredsOf(d);
		boolean isIfPred = false;
		for (Unit pred : preds) {
			if (pred instanceof IfStmt) {
				isIfPred = true;
				IfStmt ifStmt = (IfStmt) pred;
				if (d.toString().equals("expr = (soot.jimple.internal.AbstractBinopExpr) rightSide")) {
					System.out.println(d);

				}
				if (ifStmt.getTarget().equals(d)) {
					out.add(new FlowAbstraction(ifStmt, true));
				} else if (graph.getSuccsOf(ifStmt).contains(d)) {
					out.add(new FlowAbstraction(ifStmt, false));
				}
			}
		}
		out.addAll(in);
		if (isIfPred) {
			for (FlowAbstraction flow : out) {
				d.addTag(new ConditionTag(flow.getSource(), flow.isTrue()));
			}
		}
		// System.out.printf("The unit is |%s|\n", d);
		//
		// for (FlowAbstraction flow : out) {
		// System.out.printf("The if Stmt is |%s|\nThe boolean is %b\n",
		// flow.getSource(), flow.isTrue());
		// }
		// System.out.println("--------------------------------------------------------------------");
	}

	@Override
	protected Set<FlowAbstraction> newInitialFlow() {
		return new HashSet<FlowAbstraction>();
	}

	@Override
	protected Set<FlowAbstraction> entryInitialFlow() {
		return new HashSet<FlowAbstraction>();
	}

	@Override
	protected void merge(Set<FlowAbstraction> in1, Set<FlowAbstraction> in2, Set<FlowAbstraction> out) {
		for (FlowAbstraction flow1 : in1) {
			for (FlowAbstraction flow2 : in2) {
				if (flow1.getSource() == flow2.getSource() && flow1.isTrue() == flow2.isTrue()) {
					out.add(flow2);
				}
			}
		}
	}

	@Override
	protected void copy(Set<FlowAbstraction> source, Set<FlowAbstraction> dest) {
		dest.clear();
		dest.addAll(source);
	}

	public void doAnalysis() {
		// TODO Auto-generated method stub
		super.doAnalysis();
	}

	public Set<FlowAbstraction> getResults(Unit d) {
		return getFlowAfter(d);
	}

}
