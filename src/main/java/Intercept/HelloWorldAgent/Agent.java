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
import java.util.LinkedList;
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
				//long start = System.nanoTime();
				for (SootClass cls : Scene.v().getClasses()) {
					for (SootMethod mtd : cls.getMethods()) {
						if (mtd.getName().equals("flowThrough") && !mtd.getDeclaration().contains("volatile")) {
							reachableMethods.add(mtd);
							findReachableMethods(mtd, icfg, reachableMethods);
						}
					}

				}
				//System.out.println("Time elapsed = " + (System.nanoTime() - start));
				//start = System.nanoTime();
				for (SootMethod mtd : reachableMethods) {
					List<Unit> units = new ArrayList<Unit>();
					ClassData classData = new ClassData();
					Map<SootMethod, List<Unit>> filteredUnits = new HashMap<SootMethod, List<Unit>>();
					Body mtdBody = mtd.retrieveActiveBody();
					IfElseFinder finder = new IfElseFinder(mtdBody);
					//long startTime = System.nanoTime();
					finder.doAnalysis();
					//System.out.println("Ifelse finder took" + (System.nanoTime() - startTime));
					for (Unit unit : mtdBody.getUnits().stream().filter(x -> x.hasTag("ConditionTag"))
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
				//System.out.println("Method loop elapsed = " + (System.nanoTime() - start));
				// Scene.v().getApplicationClasses().forEach((cls) -> {
				// WriteToClass(cls);
				// });
				//start = System.nanoTime();
				enhanceMethod(classInformation);
				//System.out.println("Enhance method for" + classInformation + (System.nanoTime() - start));
			}
		});
		Scene.v().addBasicClass("java.beans.XMLEncoder", SootClass.BODIES);
		Scene.v().addBasicClass("soot.jimple.changeset.AnalysisInfo", SootClass.BODIES);
		Scene.v().addBasicClass("soot.jimple.changeset.AnalysisInfoTag", SootClass.BODIES);
		// Scene.v().forceResolve("java.beans.XMLEncoder", SootClass.HIERARCHY);

		PackManager.v().getPack("wjtp").add(transform);
		String[] targets = targetDir.split(",");
		//System.out.println(targets);
		File src = new File(targets[0]);
		File src2 = new File(targets[1]);
		File parent = src.getParentFile();
		File sootOutput = new File(parent, "sootOutput");
		try {
			FileUtils.copyDirectory(src, sootOutput);
			FileUtils.copyDirectory(src2, sootOutput);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Options.v().setPhaseOption("cg", "all-reachable:true");

		Main.main(new String[] { "-pp", "-process-dir", sootOutput.getAbsolutePath(), "-w", "-exclude", "javax",
				"-allow-phantom-refs", "-output-dir", sootOutput.getAbsolutePath(), "-no-bodies-for-excluded",
				"-src-prec", "only-class", "-output-format", "none", "-p", "jb", "use-original-names:true",
				"-keep-line-number" });
	}

	// java -cp "..\sootOutput" -javaagent:"C:\Projects\Java\Reviser
	// Workspace\SootAgent\target\HelloWorldAgent-0.0.1-SNAPSHOT-jar-with-dependencies.jar=C:\Users\karth\git\visuflow-uitests-analysis\bin"
	// de.visuflow.ex2.MainClass
	public static void premain(String agentArgs, Instrumentation inst) {
		tranform(agentArgs);
		System.out.println("----------------------End of Agent----------------------------------------");
	}

	private static void enhanceMethod(List<ClassData> classData) {
		// SootClass analysisInfoSootClass = createClassAttributeClass();
		// Scene.v().addClass(analysisInfoSootClass);
		// WriteToClass(analysisInfoSootClass);
		// SootClass analysisTagSootClass = createAnalysisInfoTagClass();
		// Scene.v().addClass(analysisTagSootClass);
		// WriteToClass(analysisTagSootClass);
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
					//long start = System.nanoTime();
					for (Unit unit : filteredUnits) {
						List<Tag> ifStmts = unit.getTags().stream().filter(x -> x.getName().equals("ConditionTag"))
								.collect(Collectors.toList());
						for (Tag tag : ifStmts) {
							ConditionTag conditionTag = (ConditionTag) tag;
							IfStmt ifStmt = (IfStmt) conditionTag.getIfStmt();
							int boolIntValue = (conditionTag.getBranch()) ? 1 : 0;
							Unit branch = Jimple.v().newAssignStmt(conditionRef,
									DIntConstant.v(boolIntValue, BooleanType.v()));

							// Unit lineNumberObjVal = Jimple.v().newAssignStmt(boolRef, Jimple.v()
							// .newStaticInvokeExpr(Scene.v()
							// .getMethod("<java.lang.Boolean: java.lang.Boolean valueOf(boolean)>")
							// .makeRef(), conditionRef));

							Unit lineNumberObjVal = Jimple.v().newAssignStmt(boolRef, Jimple.v().newStaticInvokeExpr(
									Scene.v().makeMethodRef(Scene.v().getSootClass("java.lang.Boolean"), "valueOf",
											Arrays.asList(new Type[] { BooleanType.v() }), RefType.v("java.lang.Boolean"), true),
									conditionRef));

							Unit jimpleVal = Jimple.v().newAssignStmt(jimpleRep,
									StringConstant.v(ifStmt.getCondition().toString()));

							// Unit lineNumberAdd = Jimple.v()
							// .newInvokeStmt(Jimple.v().newVirtualInvokeExpr(mapLocal, Scene.v().getMethod(
							// "<java.util.HashMap: java.lang.Object
							// put(java.lang.Object,java.lang.Object)>")
							// .makeRef(), jimpleRep, boolRef));

							Unit lineNumberAdd = Jimple.v()
									.newInvokeStmt(Jimple.v().newVirtualInvokeExpr(mapLocal,
											Scene.v().makeMethodRef(Scene.v().getSootClass("java.util.HashMap"), "put",
													Arrays.asList(new Type[] { RefType.v("java.lang.Object"),
															RefType.v("java.lang.Object") }),
													RefType.v("java.lang.Object"), false),
											jimpleRep, boolRef));

							// Unit printStreamOutRef = Jimple.v().newAssignStmt(printStreamLocal,
							// Jimple.v().newStaticFieldRef(Scene.v()
							// .getField("<java.lang.System: java.io.PrintStream out>").makeRef()));
							// SootMethod toCall = Scene.v()
							// .getMethod("<java.io.PrintStream: void println(java.lang.Object)>");
							// Unit printer = Jimple.v().newInvokeStmt(
							// Jimple.v().newVirtualInvokeExpr(printStreamLocal, toCall.makeRef(),
							// mapLocal));
							// Unit methodPrinter =
							// Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(
							// printStreamLocal, toCall.makeRef(),
							// StringConstant.v(method.getSignature())));

							units.insertBefore(branch, unit);
							units.insertAfter(lineNumberObjVal, branch);
							units.insertAfter(jimpleVal, lineNumberObjVal);
							units.insertAfter(lineNumberAdd, jimpleVal);
							// units.insertAfter(printStreamOutRef, lineNumberAdd);
							// units.insertAfter(printer, printStreamOutRef);
							// units.insertAfter(methodPrinter, printer);
							isExecuted = true;
						}
					}
					//System.out.println("Unit loop elapsed = " + (System.nanoTime() - start));
					//start = System.nanoTime();
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

						Unit lastParam = ((JimpleBody) methodBody).getFirstNonIdentityStmt();
						units.insertBefore(arrayListNew, lastParam);
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
					//System.out.println("Unit loop 2 elapsed = " + (System.nanoTime() - start));
				}

			}
			if (shouldWrite) {
				//long startTime = System.nanoTime();
				WriteToClass(sootClass);
				//System.out.println("Write file " + (System.nanoTime() - startTime));
			}
		}

	}

	private static void WriteToClass(SootClass sootClass) {
		try {
			String classFile = SourceLocator.v().getFileNameFor(sootClass, Options.output_format_class);
//			sootClass.getMethods().forEach((mtd) -> {
//				if (mtd.hasActiveBody()) {
//					mtd.retrieveActiveBody();
//				} else {
//					return;
//				}
//			});
			OutputStream streamOut = new JasminOutputStream(new FileOutputStream(classFile));
			PrintWriter writerOut = new PrintWriter(new OutputStreamWriter(streamOut));
			JasminClass jasminClass = new soot.jimple.JasminClass(sootClass);
			jasminClass.print(writerOut);
			writerOut.flush();
			streamOut.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	private static SootClass createClassAttributeClass() {
		SootClass sClass = new SootClass("AnalysisInfo", Modifier.PUBLIC);
		sClass.setSuperclass(Scene.v().getSootClass("java.lang.Object"));
		SootField classNameField = new SootField("className", RefType.v("java.lang.String"));
		SootField methodName = new SootField("methodName", RefType.v("java.lang.String"));
		SootField condition = new SootField("condition", RefType.v("java.util.HashMap"));
		classNameField.setDeclaringClass(sClass);
		classNameField.setDeclaringClass(sClass);
		methodName.setDeclaringClass(sClass);
		condition.setDeclaringClass(sClass);
		sClass.getFields().add(classNameField);
		sClass.getFields().add(methodName);
		sClass.getFields().add(condition);

		SootMethod constructor = new SootMethod("<init>", new LinkedList<>(), VoidType.v(), Modifier.PUBLIC);
		sClass.addMethod(constructor);
		JimpleBody body = Jimple.v().newBody(constructor);
		constructor.setActiveBody(body);
		PatchingChain<Unit> units = body.getUnits();
		Local self;
		self = Jimple.v().newLocal("self", RefType.v(sClass.getName()));
		body.getLocals().add(self);
		units.add(Jimple.v().newIdentityStmt(self, Jimple.v().newThisRef(sClass.getType())));
		units.add(Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(self,
				Scene.v().getMethod("<java.lang.Object: void <init>()>").makeRef())));
		units.add(Jimple.v().newReturnVoidStmt());

		SootMethod getClassName = new SootMethod("getClassName", Arrays.asList(new Type[] {}),
				RefType.v("java.lang.String"), Modifier.PUBLIC);
		sClass.addMethod(getClassName);
		JimpleBody getClassNameBody = Jimple.v().newBody(getClassName);
		getClassName.setActiveBody(getClassNameBody);
		PatchingChain<Unit> getClassNameUnits = getClassNameBody.getUnits();
		Local getClassNameSelf, getClassNameVar;
		getClassNameSelf = Jimple.v().newLocal("getClassNameSelf", RefType.v(sClass.getName()));
		getClassNameBody.getLocals().add(getClassNameSelf);
		getClassNameUnits.add(Jimple.v().newIdentityStmt(getClassNameSelf, Jimple.v().newThisRef(sClass.getType())));
		getClassNameVar = Jimple.v().newLocal("getClassNameVar", RefType.v("java.lang.String"));
		getClassNameBody.getLocals().add(getClassNameVar);
		getClassNameUnits.add(Jimple.v().newAssignStmt(getClassNameVar,
				Jimple.v().newInstanceFieldRef(getClassNameSelf, classNameField.makeRef())));
		getClassNameUnits.add(Jimple.v().newReturnStmt(getClassNameVar));

		SootMethod setClassName = new SootMethod("setClassName",
				Arrays.asList(new Type[] { RefType.v("java.lang.String") }), VoidType.v(), Modifier.PUBLIC);
		sClass.addMethod(setClassName);
		JimpleBody setClassNameBody = Jimple.v().newBody(setClassName);
		setClassName.setActiveBody(setClassNameBody);
		PatchingChain<Unit> setClassNameUnits = setClassNameBody.getUnits();
		Local setClassNameSelf, setClassNameVar;
		setClassNameSelf = Jimple.v().newLocal("setClassNameSelf", RefType.v(sClass.getName()));
		setClassNameBody.getLocals().add(setClassNameSelf);
		setClassNameVar = Jimple.v().newLocal("setClassNameVar", RefType.v("java.lang.String"));
		setClassNameBody.getLocals().add(setClassNameVar);
		setClassNameUnits.add(Jimple.v().newIdentityStmt(setClassNameSelf, Jimple.v().newThisRef(sClass.getType())));
		setClassNameUnits.add(Jimple.v().newIdentityStmt(setClassNameVar,
				Jimple.v().newParameterRef(RefType.v("java.lang.String"), 0)));
		setClassNameUnits.add(Jimple.v().newAssignStmt(
				Jimple.v().newInstanceFieldRef(setClassNameSelf, classNameField.makeRef()), setClassNameVar));
		setClassNameUnits.add(Jimple.v().newReturnVoidStmt());

		SootMethod getCondition = new SootMethod("getCondition", Arrays.asList(new Type[] {}),
				RefType.v("java.util.HashMap"), Modifier.PUBLIC);
		sClass.addMethod(getCondition);
		JimpleBody getConditionBody = Jimple.v().newBody(getCondition);
		getCondition.setActiveBody(getConditionBody);
		PatchingChain<Unit> getConditionUnits = getConditionBody.getUnits();
		Local getConditionSelf, getConditionVar;
		getConditionSelf = Jimple.v().newLocal("getConditionSelf", RefType.v(sClass.getName()));
		getConditionBody.getLocals().add(getConditionSelf);
		getConditionVar = Jimple.v().newLocal("getConditionVar", RefType.v("java.util.HashMap"));
		getConditionBody.getLocals().add(getConditionVar);
		getConditionUnits.add(Jimple.v().newIdentityStmt(getConditionSelf, Jimple.v().newThisRef(sClass.getType())));
		getConditionUnits.add(Jimple.v().newAssignStmt(getConditionVar,
				Jimple.v().newInstanceFieldRef(getConditionSelf, condition.makeRef())));
		getConditionUnits.add(Jimple.v().newReturnStmt(getConditionVar));

		SootMethod setCondition = new SootMethod("setCondition",
				Arrays.asList(new Type[] { RefType.v("java.util.HashMap") }), VoidType.v(), Modifier.PUBLIC);
		sClass.addMethod(setCondition);
		JimpleBody setConditionBody = Jimple.v().newBody(setCondition);
		setCondition.setActiveBody(setConditionBody);
		PatchingChain<Unit> setConditionUnits = setConditionBody.getUnits();
		Local setConditionSelf, setConditionVar;
		setConditionSelf = Jimple.v().newLocal("setConditionSelf", RefType.v(sClass.getName()));
		setConditionBody.getLocals().add(setConditionSelf);
		setConditionVar = Jimple.v().newLocal("setConditionVar", RefType.v("java.util.HashMap"));
		setConditionBody.getLocals().add(setConditionVar);
		setConditionUnits.add(Jimple.v().newIdentityStmt(setConditionSelf, Jimple.v().newThisRef(sClass.getType())));
		setConditionUnits.add(Jimple.v().newIdentityStmt(setConditionVar,
				Jimple.v().newParameterRef(RefType.v("java.util.HashMap"), 0)));
		setConditionUnits.add(Jimple.v()
				.newAssignStmt(Jimple.v().newInstanceFieldRef(setConditionSelf, condition.makeRef()), setConditionVar));
		setConditionUnits.add(Jimple.v().newReturnVoidStmt());

		SootMethod getMethodName = new SootMethod("getMethodName", Arrays.asList(new Type[] {}),
				RefType.v("java.lang.String"), Modifier.PUBLIC);
		sClass.addMethod(getMethodName);
		JimpleBody getMethodNameBody = Jimple.v().newBody(getMethodName);
		getMethodName.setActiveBody(getMethodNameBody);
		PatchingChain<Unit> getMethodNameUnits = getMethodNameBody.getUnits();

		Local getMethodNameSelf, getMethodNameVar;

		getMethodNameSelf = Jimple.v().newLocal("getMethodNameSelf", RefType.v(sClass.getName()));
		getMethodNameBody.getLocals().add(getMethodNameSelf);
		getMethodNameUnits.add(Jimple.v().newIdentityStmt(getMethodNameSelf, Jimple.v().newThisRef(sClass.getType())));

		getMethodNameVar = Jimple.v().newLocal("getMethodNameVar", RefType.v("java.lang.String"));
		getMethodNameBody.getLocals().add(getMethodNameVar);
		getMethodNameUnits.add(Jimple.v().newAssignStmt(getMethodNameVar,
				Jimple.v().newInstanceFieldRef(getMethodNameSelf, methodName.makeRef())));
		getMethodNameUnits.add(Jimple.v().newReturnStmt(getMethodNameVar));

		SootMethod setMethodName = new SootMethod("setMethodName",
				Arrays.asList(new Type[] { RefType.v("java.lang.String") }), VoidType.v(), Modifier.PUBLIC);
		sClass.addMethod(setMethodName);
		JimpleBody setMethodNameBody = Jimple.v().newBody(setMethodName);
		setMethodName.setActiveBody(setMethodNameBody);
		PatchingChain<Unit> setMethodNameUnits = setMethodNameBody.getUnits();
		Local setMethodNameSelf, setMethodNameVar;
		setMethodNameSelf = Jimple.v().newLocal("setMethodNameSelf", RefType.v(sClass.getName()));
		setMethodNameBody.getLocals().add(setMethodNameSelf);
		setMethodNameVar = Jimple.v().newLocal("setMethodNameVar", RefType.v("java.lang.String"));
		setMethodNameBody.getLocals().add(setMethodNameVar);
		setMethodNameUnits.add(Jimple.v().newIdentityStmt(setMethodNameSelf, Jimple.v().newThisRef(sClass.getType())));
		setMethodNameUnits.add(Jimple.v().newIdentityStmt(setMethodNameVar,
				Jimple.v().newParameterRef(RefType.v("java.lang.String"), 0)));
		setMethodNameUnits.add(Jimple.v().newAssignStmt(
				Jimple.v().newInstanceFieldRef(setMethodNameSelf, methodName.makeRef()), setMethodNameVar));
		setMethodNameUnits.add(Jimple.v().newReturnVoidStmt());

		return sClass;
	}

	private static SootClass createAnalysisInfoTagClass() {
		SootClass sClass = new SootClass("AnalysisInfoTag", Modifier.PUBLIC);
		sClass.setSuperclass(Scene.v().getSootClass("java.lang.Object"));
		sClass.addInterface(Scene.v().getSootClass("soot.tagkit.Tag"));
		SootField analysisInfoField = new SootField("analysisInfo", RefType.v("AnalysisInfo"));
		analysisInfoField.setDeclaringClass(sClass);
		sClass.getFields().add(analysisInfoField);

		SootMethod constructor = new SootMethod("<init>", Arrays.asList(new Type[] { RefType.v("AnalysisInfo") }),
				VoidType.v(), Modifier.PUBLIC);
		sClass.addMethod(constructor);
		JimpleBody body = Jimple.v().newBody(constructor);
		constructor.setActiveBody(body);
		PatchingChain<Unit> units = body.getUnits();
		Local self, analysisInfoVar;
		self = Jimple.v().newLocal("self", RefType.v(sClass.getName()));
		body.getLocals().add(self);
		analysisInfoVar = Jimple.v().newLocal("analysisInfoVar", RefType.v("AnalysisInfo"));
		body.getLocals().add(analysisInfoVar);
		units.add(Jimple.v().newIdentityStmt(self, Jimple.v().newThisRef(sClass.getType())));
		units.add(
				Jimple.v().newIdentityStmt(analysisInfoVar, Jimple.v().newParameterRef(RefType.v("AnalysisInfo"), 0)));
		units.add((soot.Unit) Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(self,
				Scene.v().getMethod("<java.lang.Object: void <init>()>").makeRef())));
		units.add(Jimple.v().newAssignStmt(Jimple.v().newInstanceFieldRef(self, analysisInfoField.makeRef()),
				analysisInfoVar));
		units.add(Jimple.v().newReturnVoidStmt());

		SootMethod getName = new SootMethod("getName", Arrays.asList(new Type[] {}), RefType.v("java.lang.String"),
				Modifier.PUBLIC);
		sClass.addMethod(getName);
		JimpleBody getNameBody = Jimple.v().newBody(getName);
		getName.setActiveBody(getNameBody);
		PatchingChain<Unit> getNameUnits = getNameBody.getUnits();
		Local getNameSelf, retVal;
		getNameSelf = Jimple.v().newLocal("getNameSelf", RefType.v(sClass.getName()));
		getNameBody.getLocals().add(getNameSelf);
		retVal = Jimple.v().newLocal("retVal", RefType.v("java.lang.String"));
		getNameBody.getLocals().add(retVal);
		getNameUnits.add(Jimple.v().newIdentityStmt(getNameSelf, Jimple.v().newThisRef(sClass.getType())));
		getNameUnits.add(Jimple.v().newAssignStmt(retVal, StringConstant.v(sClass.getName())));
		getNameUnits.add(Jimple.v().newReturnStmt(retVal));

		SootMethod getAnalysisInfo = new SootMethod("getAnalysisInfo", Arrays.asList(new Type[] {}),
				RefType.v("AnalysisInfo"), Modifier.PUBLIC);
		sClass.addMethod(getAnalysisInfo);
		JimpleBody getAnalysisInfoBody = Jimple.v().newBody(getAnalysisInfo);
		getAnalysisInfo.setActiveBody(getAnalysisInfoBody);
		PatchingChain<Unit> getAnalysisInfoUnits = getAnalysisInfoBody.getUnits();
		Local getAnalysisInfoSelf, getAnalysisInfoVar;
		getAnalysisInfoSelf = Jimple.v().newLocal("getAnalysisInfoSelf", RefType.v(sClass.getName()));
		getAnalysisInfoBody.getLocals().add(getAnalysisInfoSelf);
		getAnalysisInfoVar = Jimple.v().newLocal("getAnalysisInfoVar", RefType.v("AnalysisInfo"));
		getAnalysisInfoBody.getLocals().add(getAnalysisInfoVar);
		getAnalysisInfoUnits
				.add(Jimple.v().newIdentityStmt(getAnalysisInfoSelf, Jimple.v().newThisRef(sClass.getType())));
		getAnalysisInfoUnits.add(Jimple.v().newAssignStmt(getAnalysisInfoVar,
				Jimple.v().newInstanceFieldRef(getAnalysisInfoSelf, analysisInfoField.makeRef())));
		getAnalysisInfoUnits.add(Jimple.v().newReturnStmt(getAnalysisInfoVar));

		SootMethod getValue = new SootMethod("getValue", Arrays.asList(new Type[] {}), ArrayType.v(ByteType.v(), 1),
				Modifier.PUBLIC,
				Arrays.asList(new SootClass[] { Scene.v().getSootClass("soot.tagkit.AttributeValueException") }));
		sClass.addMethod(getValue);
		JimpleBody getValueBody = Jimple.v().newBody(getValue);
		getValue.setActiveBody(getValueBody);
		PatchingChain<Unit> getValueUnits = getValueBody.getUnits();
		Local getValueSelf, byteArrayOutput, objectOutputStream, analysisInfo, arr, ioException;
		getValueSelf = Jimple.v().newLocal("getValueSelf", RefType.v(sClass.getName()));
		byteArrayOutput = Jimple.v().newLocal("byteArrayOutput", RefType.v("java.io.ByteArrayOutputStream"));
		objectOutputStream = Jimple.v().newLocal("objectOutputStream", RefType.v("java.io.ObjectOutputStream"));
		analysisInfo = Jimple.v().newLocal("analysisInfo", RefType.v("AnalysisInfo"));
		arr = Jimple.v().newLocal("arr", ArrayType.v(ByteType.v(), 1));
		ioException = Jimple.v().newLocal("ioException", RefType.v("java.io.IOException"));

		getValueBody.getLocals().add(getValueSelf);
		getValueBody.getLocals().add(byteArrayOutput);
		getValueBody.getLocals().add(objectOutputStream);
		getValueBody.getLocals().add(analysisInfo);
		getValueBody.getLocals().add(arr);
		getValueBody.getLocals().add(ioException);

		getValueUnits.add(Jimple.v().newIdentityStmt(getValueSelf, Jimple.v().newThisRef(sClass.getType())));
		getValueUnits.add(Jimple.v().newAssignStmt(byteArrayOutput,
				Jimple.v().newNewExpr(RefType.v("java.io.ByteArrayOutputStream"))));
		getValueUnits.add(Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(byteArrayOutput,
				Scene.v().getMethod("<java.io.ByteArrayOutputStream: void <init>()>").makeRef())));

		// label 1
		Unit label1 = Jimple.v().newAssignStmt(objectOutputStream,
				Jimple.v().newNewExpr(RefType.v("java.io.ObjectOutputStream")));
		getValueUnits.add(label1);

		getValueUnits
				.add(Jimple.v()
						.newInvokeStmt(Jimple.v().newSpecialInvokeExpr(objectOutputStream, Scene.v()
								.getMethod("<java.io.ObjectOutputStream: void <init>(java.io.OutputStream)>").makeRef(),
								byteArrayOutput)));
		getValueUnits.add(Jimple.v().newAssignStmt(analysisInfo,
				Jimple.v().newInstanceFieldRef(getValueSelf, analysisInfoField.makeRef())));

		Jimple.v().newVirtualInvokeExpr(objectOutputStream,
				Scene.v().getMethod("<java.io.ObjectOutputStream: void writeObject(java.lang.Object)>").makeRef(),
				analysisInfo);

		Unit label4 = Jimple.v().newAssignStmt(arr, Jimple.v().newVirtualInvokeExpr(byteArrayOutput,
				Scene.v().getMethod("<java.io.ByteArrayOutputStream: byte[] toByteArray()>").makeRef()));

		Unit label2 = Jimple.v().newGotoStmt(label4);
		getValueUnits.add(label2);

		// label 3
		Unit label3 = Jimple.v().newIdentityStmt(ioException, Jimple.v().newCaughtExceptionRef());
		getValueUnits.add(label3);

		// label4
		getValueUnits.add(label4);
		getValueUnits.add(Jimple.v().newReturnStmt(arr));
		getValueBody.getTraps()
				.add(Jimple.v().newTrap(Scene.v().getSootClass("java.io.IOException"), label1, label2, label3));

		SootMethod toString = new SootMethod("toString", Arrays.asList(new Type[] {}), RefType.v("java.lang.String"),
				Modifier.PUBLIC);
		sClass.addMethod(toString);
		JimpleBody toStringBody = Jimple.v().newBody(toString);
		toString.setActiveBody(toStringBody);
		PatchingChain<Unit> toStringUnits = toStringBody.getUnits();
		Local analysiInfoTag, str, byteArrayOutputStream, xmlEncoder, analysisInfo1;
		analysiInfoTag = Jimple.v().newLocal("analysiInfoTag", RefType.v("AnalysisInfoTag"));
		str = Jimple.v().newLocal("str", RefType.v("java.lang.String"));
		byteArrayOutputStream = Jimple.v().newLocal("byteArrayOutputStream",
				RefType.v("java.io.ByteArrayOutputStream"));
		xmlEncoder = Jimple.v().newLocal("xmlEncoder", RefType.v("java.beans.XMLEncoder "));
		analysisInfo1 = Jimple.v().newLocal("analysisInfo1", RefType.v("AnalysisInfo"));

		toStringBody.getLocals().add(analysiInfoTag);
		toStringBody.getLocals().add(str);
		toStringBody.getLocals().add(byteArrayOutputStream);
		toStringBody.getLocals().add(xmlEncoder);
		toStringBody.getLocals().add(analysisInfo1);

		toStringUnits.add(Jimple.v().newIdentityStmt(analysiInfoTag, Jimple.v().newThisRef(sClass.getType())));
		toStringUnits.add(Jimple.v().newAssignStmt(byteArrayOutputStream,
				Jimple.v().newNewExpr(RefType.v("java.io.ByteArrayOutputStream"))));
		toStringUnits.add(Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(byteArrayOutputStream,
				Scene.v().getMethod("<java.io.ByteArrayOutputStream: void <init>()>").makeRef())));

		// Scene.v().loadBasicClasses();
		// Scene.v().loadNecessaryClasses();
		Scene.v().loadClassAndSupport("java.beans.XMLEncoder");

		Scene.v().getSootClass("java.beans.XMLEncoder").getMethods().forEach((mtd) -> mtd.retrieveActiveBody());
		toStringUnits
				.add(Jimple.v().newAssignStmt(xmlEncoder, Jimple.v().newNewExpr(RefType.v("java.beans.XMLEncoder"))));
		toStringUnits.add(Jimple.v()
				.newInvokeStmt(Jimple.v().newSpecialInvokeExpr(xmlEncoder,
						Scene.v().getMethod("<java.beans.XMLEncoder: void <init>(java.io.OutputStream)>").makeRef(),
						byteArrayOutputStream)));
		toStringUnits.add(Jimple.v().newAssignStmt(analysisInfo1,
				Jimple.v().newInstanceFieldRef(analysiInfoTag, analysisInfoField.makeRef())));

		toStringUnits.add(Jimple.v()
				.newInvokeStmt(Jimple.v().newVirtualInvokeExpr(xmlEncoder,
						Scene.v().getMethod("<java.beans.XMLEncoder: void writeObject(java.lang.Object)>").makeRef(),
						analysisInfo1)));

		toStringUnits.add(Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(xmlEncoder,
				Scene.v().getMethod("<java.beans.XMLEncoder: void close()>").makeRef())));

		toStringUnits.add(Jimple.v().newAssignStmt(str, Jimple.v().newVirtualInvokeExpr(byteArrayOutputStream,
				Scene.v().getMethod("<java.io.ByteArrayOutputStream: java.lang.String toString()>").makeRef())));
		toStringUnits.add(Jimple.v().newReturnStmt(str));

		return sClass;
	}
}