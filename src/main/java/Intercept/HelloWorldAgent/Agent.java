package Intercept.HelloWorldAgent;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.lang.instrument.Instrumentation;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.apache.commons.io.FileUtils;

import soot.*;
import soot.dava.internal.javaRep.DIntConstant;
import soot.jimple.*;
import soot.jimple.changeset.ConditionTag;
import soot.jimple.changeset.IfElseFinder;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.toolkits.ide.icfg.JimpleBasedInterproceduralCFG;
import soot.options.Options;
import soot.tagkit.Tag;
import soot.util.*;
import java.io.*;
import heros.InterproceduralCFG;

public class Agent {
	public static final String SuperClass = "soot.toolkits.scalar.UpdateableForwardFlowAnalysis";
	public static final String Updated = "updated";
	public static final String FlowThrough = "flowThrough";
	public static final String Volatile = "volatile";

	public static void findReachableMethods(SootMethod source, InterproceduralCFG<Unit, SootMethod> icfg,
			List<SootMethod> mtdLst) {
		if (!source.isPhantom()) {
			source.retrieveActiveBody();
			for (Unit mtdwithin : icfg.getCallsFromWithin(source)) {
				SootMethod methd;
				if (mtdwithin instanceof JAssignStmt) {
					methd = ((JAssignStmt) mtdwithin).getInvokeExpr().getMethod();
				} else {
					JInvokeStmt call = (JInvokeStmt) mtdwithin;
					methd = call.getInvokeExpr().getMethod();
				}
				if (!methd.isJavaLibraryMethod() && methd.isDeclared() && !methd.isPhantom() && methd.hasActiveBody()) {
					methd.retrieveActiveBody();
					if (!mtdLst.contains(methd)) {
						mtdLst.add(methd);
					}
					findReachableMethods(methd, icfg, mtdLst);
				}

			}
		}
	}

	public static void tranform(String targetDir) {
		G.reset();
		Transform transform = new Transform("wjtp.analysis", new SceneTransformer() {
			@Override
			protected void internalTransform(String arg0, Map arg1) {
				// ICFG along with findReachableMethods will be used later to find out
				// dependencies of a particular method.
				JimpleBasedInterproceduralCFG icfg = new JimpleBasedInterproceduralCFG();
				List<ClassData> classInformation = new ArrayList<ClassData>();
				List<SootMethod> reachableMethods = new ArrayList<SootMethod>();

				for (SootClass cls : Scene.v().getClasses()) {
					if (cls.hasSuperclass() && cls.getSuperclass().getName().equals(SuperClass)
							&& !cls.getPackageName().contains(Updated)) {
						for (SootMethod mtd : cls.getMethods()) {
							if (mtd.getName().equals(FlowThrough) && !mtd.getDeclaration().contains(Volatile)) {
								findReachableMethods(mtd, icfg, reachableMethods);
								break;
							}
						}
					}

				}
				for (SootMethod mtd : reachableMethods) {
					List<Unit> units = new ArrayList<Unit>();
					ClassData classData = new ClassData();
					Map<SootMethod, List<Unit>> filteredUnits = new HashMap<SootMethod, List<Unit>>();
					Body mtdBody = mtd.retrieveActiveBody();
					IfElseFinder finder = new IfElseFinder(mtdBody);
					finder.doAnalysis();
					for (Unit unit : mtdBody.getUnits().parallelStream().filter(x -> x.hasTag("ConditionTag"))
							.collect(Collectors.toList())) {
						units.add(unit);
					}
					filteredUnits.put(mtd, units);
					boolean isClassPresent = false;
					for (ClassData pred : classInformation) {
						if (pred.getSootClass().getName().equals(mtd.getDeclaringClass().getName())) {
							pred.getSootMethodData().put(mtd, units);
							isClassPresent = true;
							break;
						}
					}
					if (!isClassPresent) {
						classData.setSootClass(mtd.getDeclaringClass());
						classData.setSootMethodData(filteredUnits);
						classInformation.add(classData);
					}
				}

				enhanceMethod(classInformation);

			}
		});
		Scene.v().addBasicClass("java.beans.XMLEncoder", SootClass.BODIES);
		Scene.v().addBasicClass("soot.jimple.changeset.AnalysisInfo", SootClass.BODIES);
		Scene.v().addBasicClass("soot.jimple.changeset.AnalysisInfoTag", SootClass.BODIES);

		String[] targets = targetDir.split(",");
		File src = new File(targets[0]);
		File src2 = new File(targets[1]);
		File parent = src.getParentFile();
		File sootOutput = new File(parent, "sootOutput");
		try {
			FileUtils.copyDirectory(src, sootOutput);
			FileUtils.copyDirectory(src2, sootOutput);
		} catch (IOException e) {
			e.printStackTrace();
		}

		Options.v().setPhaseOption("cg", "all-reachable:true");
		Options.v().setPhaseOption("cg.spark", "on-fly-cg:true");
		PackManager.v().getPack("wjtp").add(transform);
		Main.main(new String[] { "-pp", "-process-dir", sootOutput.getAbsolutePath(), "-w", "-exclude", "javax",
				"-allow-phantom-refs", "-output-dir", sootOutput.getAbsolutePath(), "-no-bodies-for-excluded",
				"-src-prec", "only-class", "-output-format", "none", "-p", "jb", "use-original-names:true" });
	}

	public static void premain(String agentArgs, Instrumentation inst) {
		long startTime = System.nanoTime();
		tranform(agentArgs);
		System.out.println("Time taken " + (System.nanoTime() - startTime));
		System.out.println("----------------------End of Agent----------------------------------------");
	}

	private static void enhanceMethod(List<ClassData> classData) {
		for (ClassData data : classData) {
			boolean shouldWrite = false;
			SootClass sootClass = data.getSootClass();
			for (SootMethod method : data.getSootMethodData().keySet()) {
				List<Unit> filteredUnits = data.getSootMethodData().get(method);
				Body methodBody = method.getActiveBody();
				PatchingChain<Unit> units = methodBody.getUnits();
				// Tagging
				List<Local> params = methodBody.getParameterLocals().stream()
						.filter(pred -> pred.getType().getEscapedName().equals("soot.Unit"))
						.collect(Collectors.toList());
				Local unitParam = null;
				if (params != null && params.size() > 0) {
					Local mapLocal, analysisInfoLocal, analysisTagLocal, printStreamLocal;
					mapLocal = Jimple.v().newLocal("mapLocal", RefType.v("java.util.HashMap"));
					analysisInfoLocal = Jimple.v().newLocal("analysisInfoLocal",
							RefType.v("soot.jimple.changeset.AnalysisInfo"));
					analysisTagLocal = Jimple.v().newLocal("analysisTagLocal",
							RefType.v("soot.jimple.changeset.AnalysisInfoTag"));
					printStreamLocal = Jimple.v().newLocal("printStreamLocal", RefType.v("java.io.PrintStream"));
					methodBody.getLocals().add(mapLocal);
					methodBody.getLocals().add(analysisInfoLocal);
					methodBody.getLocals().add(analysisTagLocal);
					methodBody.getLocals().add(printStreamLocal);
					unitParam = params.get(0);
					Local conditionRef, boolRef, jimpleRep;
					// Add locals
					conditionRef = Jimple.v().newLocal("conditionRef", BooleanType.v());
					boolRef = Jimple.v().newLocal("boolRef", RefType.v("java.lang.Boolean"));
					jimpleRep = Jimple.v().newLocal("jimpleRep", RefType.v("java.lang.String"));
					methodBody.getLocals().add(conditionRef);
					methodBody.getLocals().add(boolRef);
					methodBody.getLocals().add(jimpleRep);

					boolean isExecuted = false;
					// Iterate over each IFStmt and add a print statement to it which prints the
					// current line number.
					if (filteredUnits.size() == 0) {
						isExecuted = true;
					}
					for (Unit unit : filteredUnits) {
						List<Tag> ifStmts = unit.getTags().parallelStream()
								.filter(x -> x.getName().equals("ConditionTag")).collect(Collectors.toList());
						for (Tag tag : ifStmts) {
							ConditionTag conditionTag = (ConditionTag) tag;
							IfStmt ifStmt = (IfStmt) conditionTag.getIfStmt();
							int boolIntValue = (conditionTag.getBranch()) ? 1 : 0;
							Unit branch = Jimple.v().newAssignStmt(conditionRef,
									DIntConstant.v(boolIntValue, BooleanType.v()));
							Unit lineNumberObjVal = Jimple.v().newAssignStmt(boolRef,
									Jimple.v().newStaticInvokeExpr(
											Scene.v().makeMethodRef(Scene.v().getSootClass("java.lang.Boolean"),
													"valueOf", Arrays.asList(new Type[] { BooleanType.v() }),
													RefType.v("java.lang.Boolean"), true),
											conditionRef));

							Unit jimpleVal = Jimple.v().newAssignStmt(jimpleRep,
									StringConstant.v(ifStmt.getCondition().toString()));
							Unit lineNumberAdd = Jimple.v()
									.newInvokeStmt(Jimple.v().newVirtualInvokeExpr(mapLocal,
											Scene.v().makeMethodRef(Scene.v().getSootClass("java.util.HashMap"), "put",
													Arrays.asList(new Type[] { RefType.v("java.lang.Object"),
															RefType.v("java.lang.Object") }),
													RefType.v("java.lang.Object"), false),
											jimpleRep, boolRef));
							units.insertBefore(branch, unit);
							units.insertAfter(lineNumberObjVal, branch);
							units.insertAfter(jimpleVal, lineNumberObjVal);
							units.insertAfter(lineNumberAdd, jimpleVal);
							isExecuted = true;
						}
					}
					if (isExecuted) {
						shouldWrite = true;
						Unit analysisInfoNew = Jimple.v().newAssignStmt(analysisInfoLocal,
								Jimple.v().newNewExpr(RefType.v("soot.jimple.changeset.AnalysisInfo")));

						;
						Unit analysisInfoInit = Jimple.v()
								.newInvokeStmt(Jimple.v().newSpecialInvokeExpr(analysisInfoLocal,
										Scene.v().makeMethodRef(
												Scene.v().getSootClass("soot.jimple.changeset.AnalysisInfo"), "<init>",
												Arrays.asList(new Type[] {}), VoidType.v(), false)));

						Unit analysisInfoTagNew = Jimple.v().newAssignStmt(analysisTagLocal,
								Jimple.v().newNewExpr(RefType.v("soot.jimple.changeset.AnalysisInfoTag")));

						Unit analysisInfoTagInit = Jimple.v().newInvokeStmt(Jimple.v()
								.newSpecialInvokeExpr(analysisTagLocal, Scene.v().makeMethodRef(
										Scene.v().getSootClass("soot.jimple.changeset.AnalysisInfoTag"), "<init>",
										Arrays.asList(new Type[] { RefType.v("soot.jimple.changeset.AnalysisInfo") }),
										VoidType.v(), false), analysisInfoLocal));

						Unit setClassName = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(analysisInfoLocal,
								Scene.v().makeMethodRef(Scene.v().getSootClass("soot.jimple.changeset.AnalysisInfo"),
										"setClassName", Arrays.asList(new Type[] { RefType.v("java.lang.String") }),
										VoidType.v(), false),
								StringConstant.v(data.getSootClass().getName())));

						Unit setCondition = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(analysisInfoLocal,
								Scene.v().makeMethodRef(Scene.v().getSootClass("soot.jimple.changeset.AnalysisInfo"),
										"setCondition", Arrays.asList(new Type[] { RefType.v("java.util.HashMap") }),
										VoidType.v(), false),
								mapLocal));

						Unit setMethodName = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(analysisInfoLocal,
								Scene.v().makeMethodRef(Scene.v().getSootClass("soot.jimple.changeset.AnalysisInfo"),
										"setMethodName", Arrays.asList(new Type[] { RefType.v("java.lang.String") }),
										VoidType.v(), false),
								StringConstant.v(method.getSignature())));

						Unit tagInterfaceInvoke = Jimple.v()
								.newInvokeStmt(Jimple.v().newInterfaceInvokeExpr(unitParam,
										Scene.v().getMethod("<soot.Unit: void addTag(soot.tagkit.Tag)>").makeRef(),
										analysisTagLocal));

						Unit arrayListNew = Jimple.v().newAssignStmt(mapLocal,
								Jimple.v().newNewExpr(RefType.v("java.util.HashMap")));

						Unit arrayListInit = Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(mapLocal,
								Scene.v().getMethod("<java.util.HashMap: void <init>()>").makeRef()));

						Unit firstStatement = ((JimpleBody) methodBody).getFirstNonIdentityStmt();
						units.insertBefore(arrayListNew, firstStatement);
						units.insertAfter(arrayListInit, arrayListNew);
						units.insertAfter(analysisInfoNew, arrayListInit);
						units.insertAfter(analysisInfoInit, analysisInfoNew);
						units.insertAfter(analysisInfoTagNew, analysisInfoInit);
						units.insertAfter(analysisInfoTagInit, analysisInfoTagNew);
						units.insertBefore(setClassName, analysisInfoTagInit);
						units.insertAfter(setCondition, setClassName);
						units.insertAfter(setMethodName, setCondition);
						units.insertAfter(tagInterfaceInvoke, analysisInfoTagInit);
					}
				}

			}
			if (shouldWrite) {
				WriteToClass(sootClass);
			}
		}

	}

	private static void WriteToClass(SootClass sootClass) {
		try {
			String classFile = SourceLocator.v().getFileNameFor(sootClass, Options.output_format_class);
			OutputStream streamOut = new JasminOutputStream(new FileOutputStream(classFile));
			PrintWriter writerOut = new PrintWriter(new OutputStreamWriter(streamOut));
			JasminClass jasminClass = new soot.jimple.JasminClass(sootClass);
			jasminClass.print(writerOut);
			writerOut.flush();
			streamOut.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}