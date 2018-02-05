package Intercept.HelloWorldAgent;

import java.util.List;
import java.util.Map;

import soot.SootClass;
import soot.SootMethod;
import soot.Unit;

public class ClassData {
	private SootClass sootClass;
	public SootClass getSootClass() {
		return sootClass;
	}
	public void setSootClass(SootClass sootClass) {
		this.sootClass = sootClass;
	}
	public Map<SootMethod, List<Unit>> getSootMethodData() {
		return sootMethodData;
	}
	public void setSootMethodData(Map<SootMethod, List<Unit>> sootMethodData) {
		this.sootMethodData = sootMethodData;
	}
	private Map<SootMethod, List<Unit>> sootMethodData;
	

}
