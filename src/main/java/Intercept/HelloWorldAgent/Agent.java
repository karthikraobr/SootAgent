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
				if (!methd.isJavaLibraryMethod() && methd.isDeclared() && !methd.isPhantom()) {
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
				List<ClassData> classDatas = new ArrayList<ClassData>();

				List<SootMethod> reachableMethods = new ArrayList<SootMethod>();
				Scene.v().getClasses().forEach((cls) -> {
					cls.getMethods().forEach((mtd) -> {
						if (mtd.getName().equals("flowThrough") && !mtd.getDeclaration().contains("volatile")) {
							findReachableMethods(mtd, icfg, reachableMethods);
						}

					});

				});

				for (SootMethod mtd : reachableMethods) {
					List<Unit> units = new ArrayList<Unit>();
					ClassData classData = new ClassData();
					Map<SootMethod, List<Unit>> filteredUnits = new HashMap<SootMethod, List<Unit>>();
					Body mtdBody = mtd.retrieveActiveBody();
					IfElseFinder finder = new IfElseFinder(mtdBody);
					finder.doAnalysis();
					for (Unit unit : mtdBody.getUnits().stream().filter(x -> x.hasTag("ConditionTag"))
							.collect(Collectors.toList())) {
						System.out.printf("The unit after condition is %s\n", unit.toString());
						units.add(unit);
					}
					filteredUnits.put(mtd, units);
					boolean isClassPresent = false;
					for (ClassData pred : classDatas) {
						if (pred.getSootClass().getName().equals(mtd.getDeclaringClass().getName())) {
							pred.getSootMethodData().put(mtd, units);
							isClassPresent = true;
							break;
						}
					}
					if (!isClassPresent) {
						classData.setSootClass(mtd.getDeclaringClass());
						classData.setSootMethodData(filteredUnits);
						classDatas.add(classData);
					}
				}
				Scene.v().getApplicationClasses().forEach((cls) -> {
					WriteToClass(cls);
				});
				enhanceMethod(classDatas);
			}
		});
		Scene.v().addBasicClass("java.beans.XMLEncoder", SootClass.BODIES);
		// Scene.v().forceResolve("java.beans.XMLEncoder", SootClass.HIERARCHY);

		PackManager.v().getPack("wjtp").add(transform);
		File src = new File(targetDir);
		File parent = src.getParentFile();
		File sootOutput = new File(parent, "sootOutput");
		try {
			FileUtils.copyDirectory(src, sootOutput);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Main.main(new String[] { "-pp", "-process-dir", targetDir, "-w", "-exclude", "javax", "-allow-phantom-refs",
				"-output-dir", sootOutput.getAbsolutePath(), "-no-bodies-for-excluded", "-src-prec", "only-class",
				"-output-format", "J", "-p", "jb", "use-original-names:true", "-keep-line-number", });
	}

	// java -cp "..\sootOutput" -javaagent:"C:\Projects\Java\Reviser
	// Workspace\SootAgent\target\HelloWorldAgent-0.0.1-SNAPSHOT-jar-with-dependencies.jar=C:\Users\karth\git\visuflow-uitests-analysis\bin"
	// de.visuflow.ex2.MainClass
	public static void premain(String agentArgs, Instrumentation inst) {
		tranform(agentArgs);
	}

	private static void enhanceMethod(List<ClassData> classData) {
		SootClass analysisInfoSootClass = createClassAttributeClass();
		Scene.v().addClass(analysisInfoSootClass);
		WriteToClass(analysisInfoSootClass);
		SootClass analysisTagSootClass = createAnalysisInfoTagClass();
		Scene.v().addClass(analysisTagSootClass);
		WriteToClass(analysisTagSootClass);
		for (ClassData data : classData) {
			SootClass sootClass = data.getSootClass();
			System.out.println("Thes soot class is " + sootClass.getName());
			createTagMethod(sootClass);
			data.getSootMethodData().forEach((method, filteredUnits) -> {
				System.out.println("Method is " + method.getSignature());
				Body methodBody = method.getActiveBody();
				PatchingChain<Unit> units = methodBody.getUnits();
				// Tagging
				Local mapLocal, analysisInfoLocal, analysisTagLocal;
				mapLocal = Jimple.v().newLocal("mapLocal", RefType.v("java.util.HashMap"));
				analysisInfoLocal = Jimple.v().newLocal("analysisInfoLocal", RefType.v("AnalysisInfo"));
				analysisTagLocal = Jimple.v().newLocal("analysisTagLocal", RefType.v("AnalysisInfoTag"));
				methodBody.getLocals().add(mapLocal);
				methodBody.getLocals().add(analysisInfoLocal);
				methodBody.getLocals().add(analysisTagLocal);

				List<Local> params = methodBody.getParameterLocals().stream()
						.filter(pred -> pred.getType().getEscapedName().equals("soot.Unit"))
						.collect(Collectors.toList());
				Local unitParam = null;
				if (params != null && params.size() > 0) {
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
					for (Unit unit : filteredUnits) {
						List<Tag> ifStmts = unit.getTags().stream().filter(x -> x.getName().equals("ConditionTag"))
								.collect(Collectors.toList());
						for (Tag tag : ifStmts) {
							ConditionTag conditionTag = (ConditionTag) tag;
							Unit ifStmt = conditionTag.getIfStmt();
							int boolIntValue = (conditionTag.getBranch()) ? 1 : 0;
							Unit branch = Jimple.v().newAssignStmt(conditionRef,
									DIntConstant.v(boolIntValue, BooleanType.v()));
							Unit lineNumberObjVal = Jimple.v().newAssignStmt(boolRef, Jimple.v()
									.newStaticInvokeExpr(Scene.v()
											.getMethod("<java.lang.Boolean: java.lang.Boolean valueOf(boolean)>")
											.makeRef(), conditionRef));

							Unit jimpleVal = Jimple.v().newAssignStmt(jimpleRep, StringConstant.v(ifStmt.toString()));

							Unit lineNumberAdd = Jimple.v()
									.newInvokeStmt(Jimple.v().newVirtualInvokeExpr(mapLocal, Scene.v().getMethod(
											"<java.util.HashMap: java.lang.Object put(java.lang.Object,java.lang.Object)>")
											.makeRef(), jimpleRep, boolRef));

							units.insertBefore(branch, unit);
							units.insertAfter(lineNumberObjVal, branch);
							units.insertAfter(jimpleVal, lineNumberObjVal);
							units.insertAfter(lineNumberAdd, jimpleVal);
							isExecuted = true;
						}
					}

					if (isExecuted) {
						Unit analysisInfoNew = Jimple.v().newAssignStmt(analysisInfoLocal,
								Jimple.v().newNewExpr(RefType.v("AnalysisInfo")));

						Unit analysisInfoInit = Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(
								analysisInfoLocal, Scene.v().getMethod("<AnalysisInfo: void <init>()>").makeRef()));

						Unit analysisInfoTagNew = Jimple.v().newAssignStmt(analysisTagLocal,
								Jimple.v().newNewExpr(RefType.v("AnalysisInfoTag")));

						Unit analysisInfoTagInit = Jimple.v()
								.newInvokeStmt(Jimple.v().newSpecialInvokeExpr(analysisTagLocal,
										Scene.v().getMethod("<AnalysisInfoTag: void <init>(AnalysisInfo)>").makeRef(),
										analysisInfoLocal));

						Unit setClassName = Jimple.v()
								.newInvokeStmt(Jimple.v().newVirtualInvokeExpr(analysisInfoLocal, Scene.v()
										.getMethod("<AnalysisInfo: void setClassName(java.lang.String)>").makeRef(),
										StringConstant.v(data.getSootClass().getName())));
						Unit setCondition = Jimple.v()
								.newInvokeStmt(Jimple.v().newVirtualInvokeExpr(analysisInfoLocal, Scene.v()
										.getMethod("<AnalysisInfo: void setCondition(java.util.HashMap)>").makeRef(),
										mapLocal));

						Unit setMethodName = Jimple.v()
								.newInvokeStmt(Jimple.v().newVirtualInvokeExpr(analysisInfoLocal, Scene.v()
										.getMethod("<AnalysisInfo: void setMethodName(java.lang.String)>").makeRef(),
										StringConstant.v(method.getName())));

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
				}

			});
			WriteToClass(sootClass);
		}

	}

	private static void WriteToClass(SootClass sootClass) {
		try {
			String classFile = SourceLocator.v().getFileNameFor(sootClass, Options.output_format_class);
			sootClass.getMethods().forEach((mtd) -> {
				mtd.retrieveActiveBody();
			});
			OutputStream streamOut = new JasminOutputStream(new FileOutputStream(classFile));
			PrintWriter writerOut = new PrintWriter(new OutputStreamWriter(streamOut));
			System.out.println(sootClass.getName());
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
		getAnalysisInfoUnits.add(Jimple.v().newIdentityStmt(getAnalysisInfoSelf, Jimple.v().newThisRef(sClass.getType())));
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

		SootMethod toString = new SootMethod("toString", Arrays.asList(new Type[] {}),
				RefType.v("java.lang.String"), Modifier.PUBLIC);
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

	private static void createTagMethod(SootClass sootClass) {
		SootMethod isUnitTagged = new SootMethod("isUnitTagged",
				Arrays.asList(new Type[] { RefType.v("soot.Unit"), RefType.v("java.lang.String"), RefType.v("java.lang.String") }), BooleanType.v(),
				Modifier.PUBLIC);
		
		JimpleBody isUnitTaggedBody = Jimple.v().newBody(isUnitTagged);
		isUnitTagged.setActiveBody(isUnitTaggedBody);
		PatchingChain<Unit> isUnitTaggedUnits = isUnitTaggedBody.getUnits();
		Local isUnitTaggedSelf, isUnitTaggedUnit, isUnitTaggedClassName, isUnitTaggedMethodName, isUnitTaggedr1,
				isUnitTaggedr2, isUnitTaggedr3, isUnitTaggedTags, isUnitTaggedtag, isUnitTaggedIterator,
				isUnitTaggedAnalysisInfoTag, isUnitTaggedAnalysisInfo, isUnitTaggedz0, isUnitTaggedz1, isUnitTaggedz2,
				isUnitTaggedz3, isUnitTaggedz4, isUnitTaggedr0;

		isUnitTaggedSelf = Jimple.v().newLocal("isUnitTaggedSelf", RefType.v(sootClass));
		isUnitTaggedUnit = Jimple.v().newLocal("isUnitTaggedUnit", RefType.v("soot.Unit"));
		isUnitTaggedClassName = Jimple.v().newLocal("isUnitTaggedClassName", RefType.v("java.lang.String"));
		isUnitTaggedMethodName = Jimple.v().newLocal("isUnitTaggedMethodName", RefType.v("java.lang.String"));
		isUnitTaggedr1 = Jimple.v().newLocal("isUnitTaggedr1", RefType.v("java.lang.String"));
		isUnitTaggedr2 = Jimple.v().newLocal("isUnitTaggedr2", RefType.v("java.lang.String"));
		isUnitTaggedr3 = Jimple.v().newLocal("isUnitTaggedr3", RefType.v("java.lang.String"));

		isUnitTaggedTags = Jimple.v().newLocal("isUnitTaggedTags", RefType.v("java.util.List"));
		isUnitTaggedtag = Jimple.v().newLocal("isUnitTaggedtag", RefType.v("soot.tagkit.Tag"));
		isUnitTaggedIterator = Jimple.v().newLocal("isUnitTaggedIterator", RefType.v("java.util.Iterator"));
		isUnitTaggedAnalysisInfoTag = Jimple.v().newLocal("isUnitTaggedAnalysisInfoTag", RefType.v("AnalysisInfoTag"));
		isUnitTaggedAnalysisInfo = Jimple.v().newLocal("isUnitTaggedAnalysisInfo", RefType.v("AnalysisInfo"));

		isUnitTaggedz0 = Jimple.v().newLocal("isUnitTaggedz0", BooleanType.v());
		isUnitTaggedz1 = Jimple.v().newLocal("isUnitTaggedz1", BooleanType.v());
		isUnitTaggedz2 = Jimple.v().newLocal("isUnitTaggedz2", BooleanType.v());
		isUnitTaggedz3 = Jimple.v().newLocal("isUnitTaggedz3", BooleanType.v());
		isUnitTaggedz4 = Jimple.v().newLocal("isUnitTaggedz4", BooleanType.v());
		isUnitTaggedr0 = Jimple.v().newLocal("isUnitTaggedr0", RefType.v("java.lang.Object"));

		isUnitTaggedBody.getLocals().add(isUnitTaggedSelf);
		isUnitTaggedBody.getLocals().add(isUnitTaggedUnit);
		isUnitTaggedBody.getLocals().add(isUnitTaggedClassName);
		isUnitTaggedBody.getLocals().add(isUnitTaggedMethodName);
		isUnitTaggedBody.getLocals().add(isUnitTaggedr1);
		isUnitTaggedBody.getLocals().add(isUnitTaggedr2);
		isUnitTaggedBody.getLocals().add(isUnitTaggedr3);
		isUnitTaggedBody.getLocals().add(isUnitTaggedTags);
		isUnitTaggedBody.getLocals().add(isUnitTaggedtag);
		isUnitTaggedBody.getLocals().add(isUnitTaggedIterator);
		isUnitTaggedBody.getLocals().add(isUnitTaggedAnalysisInfoTag);
		isUnitTaggedBody.getLocals().add(isUnitTaggedAnalysisInfo);
		isUnitTaggedBody.getLocals().add(isUnitTaggedz0);
		isUnitTaggedBody.getLocals().add(isUnitTaggedz1);
		isUnitTaggedBody.getLocals().add(isUnitTaggedz2);
		isUnitTaggedBody.getLocals().add(isUnitTaggedz3);
		isUnitTaggedBody.getLocals().add(isUnitTaggedz4);
		isUnitTaggedBody.getLocals().add(isUnitTaggedr0);

		isUnitTaggedUnits.add(Jimple.v().newIdentityStmt(isUnitTaggedSelf, Jimple.v().newThisRef(sootClass.getType())));
		isUnitTaggedUnits.add(
				Jimple.v().newIdentityStmt(isUnitTaggedUnit, Jimple.v().newParameterRef(RefType.v("soot.Unit"), 0)));
		isUnitTaggedUnits.add(Jimple.v().newIdentityStmt(isUnitTaggedClassName,
				Jimple.v().newParameterRef(RefType.v("java.lang.String"), 1)));
		isUnitTaggedUnits.add(Jimple.v().newIdentityStmt(isUnitTaggedMethodName,
				Jimple.v().newParameterRef(RefType.v("java.lang.String"), 2)));

		SootClass tagClass = Scene.v().getSootClass("soot.Tag");
		Unit isUnitTaggedz0Assign = Jimple.v().newAssignStmt(isUnitTaggedz0,
				Jimple.v().newInterfaceInvokeExpr(isUnitTaggedUnit,
						Scene.v().makeMethodRef(tagClass, "hasTag",Arrays.asList(new Type[] {RefType.v("java.lang.String")}) , BooleanType.v(), false),
						StringConstant.v("AnalysisInfoTag")));
		isUnitTaggedUnits.add(isUnitTaggedz0Assign);

		BinopExpr condition1 = Jimple.v().newEqExpr(isUnitTaggedz0, IntConstant.v(0));
		
		Unit returnStmt0 = Jimple.v().newReturnStmt(IntConstant.v(0));
		Unit IfStmt1 = Jimple.v().newIfStmt(condition1, returnStmt0);
		isUnitTaggedUnits.add(IfStmt1);
		
		SootClass unitClass = Scene.v().getSootClass("soot.Unit");
		
		
		Unit isUnitTaggedUnitAssign = Jimple.v().newAssignStmt(isUnitTaggedTags,
				Jimple.v().newInterfaceInvokeExpr(isUnitTaggedUnit,
						Scene.v().makeMethodRef(unitClass, "getTags",Arrays.asList(new Type[] {}) , RefType.v("java.util.List"), false), Arrays.asList()));
		isUnitTaggedUnits.add(isUnitTaggedUnitAssign);

        //l6 = interfaceinvoke tags.<java.util.List: java.util.Iterator iterator()>();

        //goto label3;
		Unit isUnitTaggedIteratorAssign = Jimple.v().newAssignStmt(isUnitTaggedIterator,
				Jimple.v().newInterfaceInvokeExpr(isUnitTaggedTags,
						Scene.v().getMethod("<java.util.List: java.util.Iterator iterator()>").makeRef(),
						Arrays.asList()));
		isUnitTaggedUnits.add(isUnitTaggedIteratorAssign);
		Unit isUnitTaggedz4Assign = Jimple.v().newAssignStmt(isUnitTaggedz4,
				Jimple.v().newInterfaceInvokeExpr(isUnitTaggedIterator,
						Scene.v().getMethod("<java.util.Iterator: boolean hasNext()>").makeRef(),
						Arrays.asList()));
		Unit gotoStmt = Jimple.v().newGotoStmt(isUnitTaggedz4Assign);
		isUnitTaggedUnits.add(gotoStmt);
		
		Unit isUnitTaggedroAssign = Jimple.v().newAssignStmt(isUnitTaggedr0,
				Jimple.v().newInterfaceInvokeExpr(isUnitTaggedIterator,
						Scene.v().getMethod("<java.util.Iterator: java.lang.Object next()>").makeRef(),
						Arrays.asList()));
		isUnitTaggedUnits.add(isUnitTaggedroAssign);
		
		


		Unit isUnitTaggedtagTypeCast = Jimple.v().newAssignStmt(isUnitTaggedtag,
				Jimple.v().newCastExpr(isUnitTaggedr0, RefType.v("soot.tagkit.Tag")));
		isUnitTaggedUnits.add(isUnitTaggedtagTypeCast);

		SootClass tagKitClass = Scene.v().getSootClass("soot.tagkit.Tag");
		
		
		Unit isUnitTaggedr1Assign = Jimple.v().newAssignStmt(isUnitTaggedr1,
				Jimple.v().newInterfaceInvokeExpr(isUnitTaggedtag,
						Scene.v().makeMethodRef(tagKitClass, "getName",Arrays.asList(new Type[] {}) , RefType.v("java.lang.String"), false),
						Arrays.asList()));
		isUnitTaggedUnits.add(isUnitTaggedr1Assign);

		Unit isUnitTaggedz1Assign = Jimple.v().newAssignStmt(isUnitTaggedz1,
				Jimple.v().newVirtualInvokeExpr(isUnitTaggedr1,
						Scene.v().getMethod("<java.lang.String: boolean equals(java.lang.Object)>").makeRef(),
						StringConstant.v("AnalysisInfoTag")));
		isUnitTaggedUnits.add(isUnitTaggedz1Assign);

		
		BinopExpr condition2 = Jimple.v().newEqExpr(isUnitTaggedz1, IntConstant.v(0));
		Unit IfStmt2 = Jimple.v().newIfStmt(condition2, isUnitTaggedz4Assign);
		isUnitTaggedUnits.add(IfStmt2);
		
		Unit isUnitTaggedAnalysisInfoTagAssign = Jimple.v().newAssignStmt(isUnitTaggedAnalysisInfoTag,
				Jimple.v().newCastExpr(isUnitTaggedtag, RefType.v("AnalysisInfoTag")));
		isUnitTaggedUnits.add(isUnitTaggedAnalysisInfoTagAssign);

		SootClass analysisInfoClass = Scene.v().getSootClass("AnalysisInfoTag");
		
		Unit isUnitTaggedAnalysisInfoAssign = Jimple.v().newAssignStmt(isUnitTaggedAnalysisInfo,
				Jimple.v().newVirtualInvokeExpr(isUnitTaggedAnalysisInfoTag,
						Scene.v().makeMethodRef(analysisInfoClass, "getAnalysisInfo",Arrays.asList(new Type[] {}) , RefType.v("AnalysisInfo"), false),
						Arrays.asList()));
		isUnitTaggedUnits.add(isUnitTaggedAnalysisInfoAssign);

		Unit isUnitTaggedr2Assign = Jimple.v().newAssignStmt(isUnitTaggedr2,
				Jimple.v().newVirtualInvokeExpr(isUnitTaggedAnalysisInfo,
						Scene.v().getMethod("<AnalysisInfo: java.lang.String getClassName()>").makeRef(),
						Arrays.asList()));
		isUnitTaggedUnits.add(isUnitTaggedr2Assign);

		Unit isUnitTaggedz2Assign = Jimple.v().newAssignStmt(isUnitTaggedz2,
				Jimple.v().newVirtualInvokeExpr(isUnitTaggedr2,
						Scene.v().getMethod("<java.lang.String: boolean equals(java.lang.Object)>").makeRef(),
						isUnitTaggedClassName));
		isUnitTaggedUnits.add(isUnitTaggedz2Assign);
		
		Unit returnStmt1 = Jimple.v().newReturnStmt(IntConstant.v(1));
		BinopExpr condition3 = Jimple.v().newEqExpr(isUnitTaggedz2, IntConstant.v(0));
		Unit IfStmt3 = Jimple.v().newIfStmt(condition3, returnStmt1);
		isUnitTaggedUnits.add(IfStmt3);
		
		Unit isUnitTaggedr3Assign = Jimple.v().newAssignStmt(isUnitTaggedr3,
				Jimple.v().newVirtualInvokeExpr(isUnitTaggedAnalysisInfo,
						Scene.v().getMethod("<AnalysisInfo: java.lang.String getMethodName()>").makeRef(),
						Arrays.asList()));
		isUnitTaggedUnits.add(isUnitTaggedr3Assign);

		Unit isUnitTaggedz3Assign = Jimple.v().newAssignStmt(isUnitTaggedz3,
				Jimple.v().newVirtualInvokeExpr(isUnitTaggedr3,
						Scene.v().getMethod("<java.lang.String: boolean equals(java.lang.Object)>").makeRef(),
						isUnitTaggedMethodName));
		isUnitTaggedUnits.add(isUnitTaggedz3Assign);
		
		BinopExpr condition4 = Jimple.v().newNeExpr(isUnitTaggedz3, IntConstant.v(0));
		Unit IfStmt4 = Jimple.v().newIfStmt(condition4, isUnitTaggedz4Assign);
		isUnitTaggedUnits.add(IfStmt4);
		
		isUnitTaggedUnits.add(returnStmt1);

		isUnitTaggedUnits.add(isUnitTaggedz4Assign);
		
		BinopExpr condition5 = Jimple.v().newNeExpr(isUnitTaggedz4, IntConstant.v(0));
		Unit IfStmt5 = Jimple.v().newIfStmt(condition5, isUnitTaggedroAssign);
		isUnitTaggedUnits.add(IfStmt5);
		
		isUnitTaggedUnits.add(returnStmt0);
		
		sootClass.addMethod(isUnitTagged);

	}
}
