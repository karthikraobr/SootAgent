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
import soot.dava.toolkits.base.AST.transformations.VoidReturnRemover;
import soot.jimple.*;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.toolkits.ide.icfg.JimpleBasedInterproceduralCFG;
import soot.options.Options;
import soot.util.*;
import java.io.*;
import heros.InterproceduralCFG;

public class Agent {

	public static void findReachableMethods(SootMethod source, InterproceduralCFG<Unit, SootMethod> icfg,
			ArrayList<SootMethod> mtdLst) {
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

	public static void tranform() {
		G.reset();
		Transform transform = new Transform("wjtp.analysis", new SceneTransformer() {
			@Override
			protected void internalTransform(String arg0, Map arg1) {
				// ICFG along with findReachableMethods will be used later to find out
				// dependencies of a particular method.
				JimpleBasedInterproceduralCFG icfg = new JimpleBasedInterproceduralCFG();
				List<ClassData> lstClassData = new ArrayList<ClassData>();

				ArrayList<SootMethod> arr = new ArrayList<SootMethod>();
				// Iterate over the classes and methods and find units of type IfStmt
				Scene.v().getClasses().forEach((cls) -> {
					cls.getMethods().forEach((mtd) -> {
						if (mtd.getName().equals("flowThrough") && !mtd.getDeclaration().contains("volatile")) {
							findReachableMethods(mtd, icfg, arr);
						}

					});

				});

				
				for (SootMethod mtd : arr) {
					List<Unit> unts = new ArrayList<Unit>();
					ClassData classData = new ClassData();
					Map<SootMethod, List<Unit>> filteredUnit = new HashMap<SootMethod, List<Unit>>();
					Body mtdBody = mtd.retrieveActiveBody();
					for (soot.Unit unit : mtdBody.getUnits()) {
						// if (unit instanceof IfStmt || unit instanceof GotoStmt) { testing
						if (unit instanceof IfStmt) {

							unts.add(unit);

							System.out.printf("Unit %s at lineNumber %d\n", unit.toString(),
									unit.getJavaSourceStartLineNumber());
						}
					}
					filteredUnit.put(mtd, unts);
					boolean isClassPresent = false;
					for (ClassData pred : lstClassData) {
						if (pred.getSootClass().getName().equals(mtd.getDeclaringClass().getName())) {
							pred.getSootMethodData().put(mtd, unts);
							isClassPresent = true;
							break;
						}
					}
					if (!isClassPresent) {
						classData.setSootClass(mtd.getDeclaringClass());
						classData.setSootMethodData(filteredUnit);
						lstClassData.add(classData);
					}
				}
				Scene.v().getApplicationClasses().forEach((cls) -> {
					WriteToClass(cls);
				});
				enhanceMethod(lstClassData);
			}
		});
		Scene.v().addBasicClass("java.beans.XMLEncoder", SootClass.BODIES);
		// Scene.v().forceResolve("java.beans.XMLEncoder", SootClass.HIERARCHY);

		PackManager.v().getPack("wjtp").add(transform);
		String targetDir = "C:\\Users\\karth\\git\\visuflow-uitests-analysis\\bin";
		File src = new File(targetDir);
		File sootOutput = new File("sootOutput");
		try {
			FileUtils.copyDirectory(src, sootOutput);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Main.main(new String[] { "-pp", "-process-dir", targetDir, "-w", "-exclude", "javax", "-allow-phantom-refs",
				"-no-bodies-for-excluded", "-src-prec", "only-class", "-output-format", "J", "-p", "jb",
				"use-original-names:true", "-keep-line-number", });
	}

	public static void premain(String agentArgs, Instrumentation inst) {
		tranform();
	}

	private static void enhanceMethod(List<ClassData> classData) {
		SootClass analysisInfoSC = createClassAttributeClass(classData.get(0).getSootClass().getJavaPackageName());
		Scene.v().addClass(analysisInfoSC);
		WriteToClass(analysisInfoSC);
		SootClass analysisTagSC = createAnalysisInfoTagClass(classData.get(0).getSootClass().getJavaPackageName());
		Scene.v().addClass(analysisTagSC);
		WriteToClass(analysisTagSC);
		// classData.forEach((data) ->
		for (ClassData data : classData) {
			SootClass sootClass = data.getSootClass();
			System.out.println("Thes soot class is " + sootClass.getName());
			data.getSootMethodData().forEach((mtd, fltr) -> {
				System.out.println("Method is "+mtd.getSignature());
				Body mtdBody = mtd.getActiveBody();
				PatchingChain<Unit> units = mtdBody.getUnits();
				// Tagging
				Local arrayLocal, analysisInfoLocal, analysisTagLocal;
				arrayLocal = Jimple.v().newLocal("arrayLocal", RefType.v("java.util.HashMap"));
				analysisInfoLocal = Jimple.v().newLocal("analysisInfoLocal",
						RefType.v(data.getSootClass().getPackageName() + ".AnalysisInfo"));
				analysisTagLocal = Jimple.v().newLocal("analysisTagLocal",
						RefType.v(data.getSootClass().getPackageName() + ".AnalysisInfoTag"));
				mtdBody.getLocals().add(arrayLocal);
				mtdBody.getLocals().add(analysisInfoLocal);
				mtdBody.getLocals().add(analysisTagLocal);

				List<Local> params = mtdBody.getParameterLocals().stream()
						.filter(pred -> pred.getType().getEscapedName().equals("soot.Unit"))
						.collect(Collectors.toList());
				Local unitParam = null;
				if (params != null && params.size() > 0) {
					unitParam = params.get(0);
					Local stmtLineNumberRef, intObjRes, jimpleRep;
					// Add locals
					stmtLineNumberRef = Jimple.v().newLocal("stmtLineNumberRef", IntType.v());
					intObjRes = Jimple.v().newLocal("stmtLineNumberRef", RefType.v("java.lang.Integer"));
					jimpleRep = Jimple.v().newLocal("jimpleRep", RefType.v("java.lang.String"));
					mtdBody.getLocals().add(stmtLineNumberRef);
					mtdBody.getLocals().add(intObjRes);
					mtdBody.getLocals().add(jimpleRep);

					boolean isExecuted = false;
					// Iterate over each IFStmt and add a print statement to it which prints the
					// current line number.
					for (Unit unit : fltr) {
						Unit actualLineNumber = Jimple.v().newAssignStmt(stmtLineNumberRef,
								IntConstant.v(unit.getJavaSourceStartLineNumber()));
						Unit lineNumberObjVal = Jimple.v().newAssignStmt(intObjRes,
								Jimple.v().newStaticInvokeExpr(Scene.v()
										.getMethod("<java.lang.Integer: java.lang.Integer valueOf(int)>").makeRef(),
										stmtLineNumberRef));

						Unit jimpleVal = Jimple.v().newAssignStmt(jimpleRep, StringConstant.v(unit.toString()));

						Unit lineNumberAdd = Jimple.v()
								.newInvokeStmt(Jimple.v().newVirtualInvokeExpr(arrayLocal, Scene.v().getMethod(
										"<java.util.HashMap: java.lang.Object put(java.lang.Object,java.lang.Object)>")
										.makeRef(), intObjRes, jimpleRep));

						// Unit jimpleRepresentation = Jimple.v().newAssignStmt(jimpleRep,
						// StringConstant.v(unit.toString()));
						// Insert Units in the right order.

						if (units.contains(unit)) {
							if (!(((IfStmt) unit).getTarget() instanceof ReturnVoidStmt)) {
								units.insertAfter(actualLineNumber, units.getSuccOf(((IfStmt) unit).getTarget()));
								
							} else {
								units.insertAfter(actualLineNumber, units.getSuccOf(unit));
							}
							//units.insertBefore(actualLineNumber, ((IfStmt) unit).getTarget());
							// units.insertAfter(actualLineNumber, unit);
							units.insertAfter(lineNumberObjVal, actualLineNumber);
							units.insertAfter(jimpleVal, lineNumberObjVal);
							units.insertAfter(lineNumberAdd, jimpleVal);
							// units.insertAfter(jimpleRepresentation, lineNumberAdd);
							isExecuted = true;
						}
					}
					if(isExecuted) {
					Unit analysisInfoNew = Jimple.v().newAssignStmt(analysisInfoLocal, Jimple.v()
							.newNewExpr(RefType.v(data.getSootClass().getPackageName() + ".AnalysisInfo")));

					Unit analysisInfoInit = Jimple.v()
							.newInvokeStmt(Jimple.v().newSpecialInvokeExpr(analysisInfoLocal,
									Scene.v().getMethod("<" + data.getSootClass().getPackageName()
											+ ".AnalysisInfo: void <init>()>").makeRef()));

					Unit analysisInfoTagNew = Jimple.v().newAssignStmt(analysisTagLocal,
							Jimple.v().newNewExpr(
									RefType.v(data.getSootClass().getPackageName() + ".AnalysisInfoTag")));

					Unit analysisInfoTagInit = Jimple.v()
							.newInvokeStmt(Jimple.v().newSpecialInvokeExpr(analysisTagLocal,
									Scene.v().getMethod("<" + data.getSootClass().getPackageName()
											+ ".AnalysisInfoTag: void <init>("
											+ data.getSootClass().getPackageName() + ".AnalysisInfo)>")
											.makeRef(),
									analysisInfoLocal));

					Unit setClassName = Jimple.v()
							.newInvokeStmt(Jimple.v().newVirtualInvokeExpr(analysisInfoLocal,
									Scene.v()
											.getMethod("<" + data.getSootClass().getJavaPackageName()
													+ ".AnalysisInfo: void setClassName(java.lang.String)>")
											.makeRef(),
									StringConstant.v(data.getSootClass().getName())));
					Unit setLineNumbers = Jimple.v()
							.newInvokeStmt(Jimple.v().newVirtualInvokeExpr(analysisInfoLocal,
									Scene.v().getMethod("<" + data.getSootClass().getJavaPackageName()
											+ ".AnalysisInfo: void setLineNumber(java.util.HashMap)>")
											.makeRef(),
									arrayLocal));

					Unit setMethodName = Jimple.v()
							.newInvokeStmt(Jimple.v().newVirtualInvokeExpr(analysisInfoLocal,
									Scene.v().getMethod("<" + data.getSootClass().getJavaPackageName()
											+ ".AnalysisInfo: void setMethodName(java.lang.String)>")
											.makeRef(),
									StringConstant.v(mtd.getName())));

					Unit tagInterfaceInvoke = Jimple.v()
							.newInvokeStmt(Jimple.v().newInterfaceInvokeExpr(unitParam, Scene.v()
									.getMethod("<soot.Unit: void addTag(soot.tagkit.Tag)>").makeRef(),
									analysisTagLocal));
					
					Unit arrayListNew = Jimple.v().newAssignStmt(arrayLocal,
							Jimple.v().newNewExpr(RefType.v("java.util.HashMap")));

					Unit arrayListInit = Jimple.v()
							.newInvokeStmt(Jimple.v().newSpecialInvokeExpr(arrayLocal,
									Scene.v().getMethod("<java.util.HashMap: void <init>()>").makeRef()));

					Unit lastParam = ((JimpleBody) mtdBody).getFirstNonIdentityStmt();
					units.insertBefore(arrayListNew, lastParam);
					units.insertAfter(arrayListInit, arrayListNew);
					units.insertAfter(analysisInfoNew, arrayListInit);
					units.insertAfter(analysisInfoInit, analysisInfoNew);
					units.insertAfter(analysisInfoTagNew, analysisInfoInit);
					units.insertAfter(analysisInfoTagInit, analysisInfoTagNew);
					units.insertBefore(setClassName, analysisInfoTagInit);
					units.insertAfter(setLineNumbers, setClassName);
					units.insertAfter(setMethodName, setLineNumbers);
					units.insertAfter(tagInterfaceInvoke, analysisInfoTagInit);
					}

				}
				
			});
			WriteToClass(sootClass);
		} // );

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

	private static SootClass createClassAttributeClass(String packageName) {

		SootClass sClass = new SootClass(packageName + "." + "AnalysisInfo", Modifier.PUBLIC);
		sClass.setSuperclass(Scene.v().getSootClass("java.lang.Object"));
		SootField classNameField = new SootField("className", RefType.v("java.lang.String"));
		SootField methodName = new SootField("methodName", RefType.v("java.lang.String"));
		SootField unitRepresentation = new SootField("unitRepresentation", RefType.v("java.lang.String"));
		SootField line = new SootField("line", RefType.v("java.util.HashMap"));
		classNameField.setDeclaringClass(sClass);
		classNameField.setDeclaringClass(sClass);
		methodName.setDeclaringClass(sClass);
		unitRepresentation.setDeclaringClass(sClass);
		line.setDeclaringClass(sClass);
		sClass.getFields().add(classNameField);
		sClass.getFields().add(methodName);
		sClass.getFields().add(unitRepresentation);
		sClass.getFields().add(line);

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

		SootMethod getLine = new SootMethod("getLineNumber", Arrays.asList(new Type[] {}),
				RefType.v("java.util.HashMap"), Modifier.PUBLIC);
		sClass.addMethod(getLine);
		JimpleBody getLineNumberBody = Jimple.v().newBody(getLine);
		getLine.setActiveBody(getLineNumberBody);
		PatchingChain<Unit> getLineNumberUnits = getLineNumberBody.getUnits();
		Local getLineNumberSelf, getLineNumberVar;
		getLineNumberSelf = Jimple.v().newLocal("getLineNumberSelf", RefType.v(sClass.getName()));
		getLineNumberBody.getLocals().add(getLineNumberSelf);
		getLineNumberVar = Jimple.v().newLocal("getLineNumberVar", RefType.v("java.util.HashMap"));
		getLineNumberBody.getLocals().add(getLineNumberVar);
		getLineNumberUnits.add(Jimple.v().newIdentityStmt(getLineNumberSelf, Jimple.v().newThisRef(sClass.getType())));
		getLineNumberUnits.add(Jimple.v().newAssignStmt(getLineNumberVar,
				Jimple.v().newInstanceFieldRef(getLineNumberSelf, line.makeRef())));
		getLineNumberUnits.add(Jimple.v().newReturnStmt(getLineNumberVar));

		SootMethod setLine = new SootMethod("setLineNumber",
				Arrays.asList(new Type[] { RefType.v("java.util.HashMap") }), VoidType.v(), Modifier.PUBLIC);
		sClass.addMethod(setLine);
		JimpleBody setLineNumberBody = Jimple.v().newBody(setLine);
		setLine.setActiveBody(setLineNumberBody);
		PatchingChain<Unit> setLineNumberUnits = setLineNumberBody.getUnits();
		Local setLineNumberSelf, setLineNumberVar;
		setLineNumberSelf = Jimple.v().newLocal("setLineNumberSelf", RefType.v(sClass.getName()));
		setLineNumberBody.getLocals().add(setLineNumberSelf);
		setLineNumberVar = Jimple.v().newLocal("setLineNumberVar", RefType.v("java.util.HashMap"));
		setLineNumberBody.getLocals().add(setLineNumberVar);
		setLineNumberUnits.add(Jimple.v().newIdentityStmt(setLineNumberSelf, Jimple.v().newThisRef(sClass.getType())));
		setLineNumberUnits.add(Jimple.v().newIdentityStmt(setLineNumberVar,
				Jimple.v().newParameterRef(RefType.v("java.util.HashMap"), 0)));
		setLineNumberUnits.add(Jimple.v()
				.newAssignStmt(Jimple.v().newInstanceFieldRef(setLineNumberSelf, line.makeRef()), setLineNumberVar));
		setLineNumberUnits.add(Jimple.v().newReturnVoidStmt());

		SootMethod getUnitRepresentation = new SootMethod("getUnitRepresentation", Arrays.asList(new Type[] {}),
				RefType.v("java.lang.String"), Modifier.PUBLIC);
		sClass.addMethod(getUnitRepresentation);
		JimpleBody getUnitRepresentationBody = Jimple.v().newBody(getUnitRepresentation);
		getUnitRepresentation.setActiveBody(getUnitRepresentationBody);
		PatchingChain<Unit> getUnitRepresentationUnits = getUnitRepresentationBody.getUnits();

		Local getUnitRepresentationSelf, getUnitRepresentationVar;

		getUnitRepresentationSelf = Jimple.v().newLocal("getUnitRepresentationSelf", RefType.v(sClass.getName()));
		getUnitRepresentationBody.getLocals().add(getUnitRepresentationSelf);
		getUnitRepresentationUnits
				.add(Jimple.v().newIdentityStmt(getUnitRepresentationSelf, Jimple.v().newThisRef(sClass.getType())));

		getUnitRepresentationVar = Jimple.v().newLocal("getUnitRepresentationVar", RefType.v("java.lang.String"));
		getUnitRepresentationBody.getLocals().add(getUnitRepresentationVar);
		getUnitRepresentationUnits.add(Jimple.v().newAssignStmt(getUnitRepresentationVar,
				Jimple.v().newInstanceFieldRef(getUnitRepresentationSelf, unitRepresentation.makeRef())));
		getUnitRepresentationUnits.add(Jimple.v().newReturnStmt(getUnitRepresentationVar));

		SootMethod setUnitRepresentation = new SootMethod("setUnitRepresentation",
				Arrays.asList(new Type[] { RefType.v("java.lang.String") }), VoidType.v(), Modifier.PUBLIC);
		sClass.addMethod(setUnitRepresentation);
		JimpleBody setUnitRepresentationBody = Jimple.v().newBody(setUnitRepresentation);
		setUnitRepresentation.setActiveBody(setUnitRepresentationBody);
		PatchingChain<Unit> setUnitRepresentationUnits = setUnitRepresentationBody.getUnits();
		Local setUnitRepresentationSelf, setUnitRepresentationVar;
		setUnitRepresentationSelf = Jimple.v().newLocal("setUnitRepresentationSelf", RefType.v(sClass.getName()));
		setUnitRepresentationBody.getLocals().add(setUnitRepresentationSelf);
		setUnitRepresentationVar = Jimple.v().newLocal("setUnitRepresentationVar", RefType.v("java.lang.String"));
		setUnitRepresentationBody.getLocals().add(setUnitRepresentationVar);
		setUnitRepresentationUnits
				.add(Jimple.v().newIdentityStmt(setUnitRepresentationSelf, Jimple.v().newThisRef(sClass.getType())));
		setUnitRepresentationUnits.add(Jimple.v().newIdentityStmt(setUnitRepresentationVar,
				Jimple.v().newParameterRef(RefType.v("java.lang.String"), 0)));
		setUnitRepresentationUnits.add(Jimple.v().newAssignStmt(
				Jimple.v().newInstanceFieldRef(setUnitRepresentationSelf, unitRepresentation.makeRef()),
				setUnitRepresentationVar));
		setUnitRepresentationUnits.add(Jimple.v().newReturnVoidStmt());

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

	private static SootClass createAnalysisInfoTagClass(String packageName) {
		SootClass sClass = new SootClass(packageName + "." + "AnalysisInfoTag", Modifier.PUBLIC);
		sClass.setSuperclass(Scene.v().getSootClass("java.lang.Object"));
		sClass.addInterface(Scene.v().getSootClass("soot.tagkit.Tag"));
		SootField analysisInfoField = new SootField("analysisInfo", RefType.v(packageName + ".AnalysisInfo"));
		analysisInfoField.setDeclaringClass(sClass);
		sClass.getFields().add(analysisInfoField);

		SootMethod constructor = new SootMethod("<init>",
				Arrays.asList(new Type[] { RefType.v(packageName + ".AnalysisInfo") }), VoidType.v(), Modifier.PUBLIC);
		sClass.addMethod(constructor);
		JimpleBody body = Jimple.v().newBody(constructor);
		constructor.setActiveBody(body);
		PatchingChain<Unit> units = body.getUnits();
		Local self, analysisInfoVar;
		self = Jimple.v().newLocal("self", RefType.v(sClass.getName()));
		body.getLocals().add(self);
		analysisInfoVar = Jimple.v().newLocal("analysisInfoVar", RefType.v(packageName + ".AnalysisInfo"));
		body.getLocals().add(analysisInfoVar);
		units.add(Jimple.v().newIdentityStmt(self, Jimple.v().newThisRef(sClass.getType())));
		units.add(Jimple.v().newIdentityStmt(analysisInfoVar,
				Jimple.v().newParameterRef(RefType.v(packageName + ".AnalysisInfo"), 0)));
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
		analysisInfo = Jimple.v().newLocal("analysisInfo", RefType.v(packageName + ".AnalysisInfo"));
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

		SootMethod getAnalysisInfo = new SootMethod("toString", Arrays.asList(new Type[] {}),
				RefType.v("java.lang.String"), Modifier.PUBLIC);
		sClass.addMethod(getAnalysisInfo);
		JimpleBody getAnalysisInfoBody = Jimple.v().newBody(getAnalysisInfo);
		getAnalysisInfo.setActiveBody(getAnalysisInfoBody);
		PatchingChain<Unit> getAnalysisInfoUnits = getAnalysisInfoBody.getUnits();
		Local analysiInfoTag, str, byteArrayOutputStream, xmlEncoder, analysisInfo1;
		analysiInfoTag = Jimple.v().newLocal("analysiInfoTag", RefType.v(packageName + ".AnalysisInfoTag"));
		str = Jimple.v().newLocal("str", RefType.v("java.lang.String"));
		byteArrayOutputStream = Jimple.v().newLocal("byteArrayOutputStream",
				RefType.v("java.io.ByteArrayOutputStream"));
		xmlEncoder = Jimple.v().newLocal("xmlEncoder", RefType.v("java.beans.XMLEncoder "));
		analysisInfo1 = Jimple.v().newLocal("analysisInfo1", RefType.v(packageName + ".AnalysisInfo"));

		getAnalysisInfoBody.getLocals().add(analysiInfoTag);
		getAnalysisInfoBody.getLocals().add(str);
		getAnalysisInfoBody.getLocals().add(byteArrayOutputStream);
		getAnalysisInfoBody.getLocals().add(xmlEncoder);
		getAnalysisInfoBody.getLocals().add(analysisInfo1);

		getAnalysisInfoUnits.add(Jimple.v().newIdentityStmt(analysiInfoTag, Jimple.v().newThisRef(sClass.getType())));
		getAnalysisInfoUnits.add(Jimple.v().newAssignStmt(byteArrayOutputStream,
				Jimple.v().newNewExpr(RefType.v("java.io.ByteArrayOutputStream"))));
		getAnalysisInfoUnits.add(Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(byteArrayOutputStream,
				Scene.v().getMethod("<java.io.ByteArrayOutputStream: void <init>()>").makeRef())));

		// Scene.v().loadBasicClasses();
		// Scene.v().loadNecessaryClasses();
		Scene.v().loadClassAndSupport("java.beans.XMLEncoder");

		Scene.v().getSootClass("java.beans.XMLEncoder").getMethods().forEach((mtd) -> mtd.retrieveActiveBody());
		getAnalysisInfoUnits
				.add(Jimple.v().newAssignStmt(xmlEncoder, Jimple.v().newNewExpr(RefType.v("java.beans.XMLEncoder"))));
		getAnalysisInfoUnits.add(Jimple.v()
				.newInvokeStmt(Jimple.v().newSpecialInvokeExpr(xmlEncoder,
						Scene.v().getMethod("<java.beans.XMLEncoder: void <init>(java.io.OutputStream)>").makeRef(),
						byteArrayOutputStream)));
		getAnalysisInfoUnits.add(Jimple.v().newAssignStmt(analysisInfo1,
				Jimple.v().newInstanceFieldRef(analysiInfoTag, analysisInfoField.makeRef())));

		getAnalysisInfoUnits.add(Jimple.v()
				.newInvokeStmt(Jimple.v().newVirtualInvokeExpr(xmlEncoder,
						Scene.v().getMethod("<java.beans.XMLEncoder: void writeObject(java.lang.Object)>").makeRef(),
						analysisInfo1)));

		getAnalysisInfoUnits.add(Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(xmlEncoder,
				Scene.v().getMethod("<java.beans.XMLEncoder: void close()>").makeRef())));

		getAnalysisInfoUnits.add(Jimple.v().newAssignStmt(str, Jimple.v().newVirtualInvokeExpr(byteArrayOutputStream,
				Scene.v().getMethod("<java.io.ByteArrayOutputStream: java.lang.String toString()>").makeRef())));
		getAnalysisInfoUnits.add(Jimple.v().newReturnStmt(str));

		return sClass;
	}

}
