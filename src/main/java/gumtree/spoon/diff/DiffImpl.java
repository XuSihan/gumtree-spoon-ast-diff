package gumtree.spoon.diff;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.stream.Collectors;

import org.apache.commons.csv.CSVFormat;
import org.apache.commons.csv.CSVPrinter;

import com.github.gumtreediff.actions.ActionGenerator;
import com.github.gumtreediff.actions.model.Action;
import com.github.gumtreediff.actions.model.Delete;
import com.github.gumtreediff.actions.model.Insert;
import com.github.gumtreediff.actions.model.Move;
import com.github.gumtreediff.actions.model.Update;
import com.github.gumtreediff.matchers.CompositeMatchers;
import com.github.gumtreediff.matchers.MappingStore;
import com.github.gumtreediff.matchers.Matcher;
import com.github.gumtreediff.tree.ITree;
import com.github.gumtreediff.tree.TreeContext;

import gumtree.spoon.builder.SpoonGumTreeBuilder;
import gumtree.spoon.diff.operations.DeleteOperation;
import gumtree.spoon.diff.operations.InsertOperation;
import gumtree.spoon.diff.operations.MoveOperation;
import gumtree.spoon.diff.operations.Operation;
import gumtree.spoon.diff.operations.OperationKind;
import gumtree.spoon.diff.operations.UpdateOperation;
import spoon.reflect.code.CtArrayAccess;
import spoon.reflect.code.CtAssert;
import spoon.reflect.code.CtAssignment;
import spoon.reflect.code.CtComment;
import spoon.reflect.code.CtConditional;
import spoon.reflect.code.CtExecutableReferenceExpression;
import spoon.reflect.code.CtFieldAccess;
import spoon.reflect.code.CtFor;
import spoon.reflect.code.CtIf;
import spoon.reflect.code.CtInvocation;
import spoon.reflect.code.CtLiteral;
import spoon.reflect.code.CtLocalVariable;
import spoon.reflect.code.CtLoop;
import spoon.reflect.code.CtStatement;
import spoon.reflect.code.CtSwitch;
import spoon.reflect.code.CtTypeAccess;
import spoon.reflect.code.CtVariableAccess;
import spoon.reflect.code.CtWhile;
import spoon.reflect.declaration.CtAnnotation;
import spoon.reflect.declaration.CtAnnotationType;
//import spoon.reflect.code.CtLocalVariable;
//import spoon.reflect.code.CtLocalVariable;
import spoon.reflect.declaration.CtClass;
import spoon.reflect.declaration.CtConstructor;
import spoon.reflect.declaration.CtElement;
import spoon.reflect.declaration.CtExecutable;
import spoon.reflect.declaration.CtMethod;
import spoon.reflect.declaration.CtModifiable;
import spoon.reflect.declaration.CtPackage;
import spoon.reflect.declaration.CtType;
import spoon.reflect.declaration.CtTypedElement;
import spoon.reflect.declaration.CtVariable;
//import spoon.reflect.factory.Factory;
//import spoon.reflect.declaration.CtMethod;
//import spoon.reflect.declaration.CtAnnotation;
import spoon.reflect.visitor.filter.TypeFilter;

/**
 * @author Matias Martinez, matias.martinez@inria.fr
 */
public class DiffImpl implements Diff {
	// Name of Extracted Method
	String Name_Ext_Mtd;
	// Name of Source Method
	String Name_Src_Mtd;
	// Extracted code
	String Extracted_Code;

	List<CtMethod> callMethod = new ArrayList<CtMethod>(); // after version里的source method
	List<CtMethod> sourceMethod = new ArrayList<CtMethod>(); // before version里的source method
	List<CtElement> deleteStuff = new ArrayList<CtElement>(); // before version里source
																														// method被delete的code
	CtMethod extracted_Method; // extracted method
	CtElement deleted; // deleted code

	// common variable declaration
	List<CtVariable> deletedVariable;
	List<CtVariable> srcVariable;
	List<CtVariable> commonVariable;

	// common variable access
	List<CtVariableAccess> delVarAcc;
	List<CtVariableAccess> srcVarAcc;
	List<CtVariableAccess> commonVariableAccess;

	// common field access
	List<CtFieldAccess> delFieldAcc;
	List<CtFieldAccess> srcFieldAcc;
	List<CtFieldAccess> commonFieldAccess;

	// common invocation
	List<CtInvocation> delInvo;
	List<CtInvocation> srcInvo;
	List<CtInvocation> commonInvo;

	// common field access
	List<CtTypeAccess> delTypeAcc;
	List<CtTypeAccess> srcTypeAcc;
	List<CtTypeAccess> commonTypeAccess;

	// common typed element
	List<CtTypedElement> delTypedEle;
	List<CtTypedElement> srcTypedEle;
	List<CtTypedElement> commonTypedElement;

	// common modifiable
	List<CtModifiable> delMod;
	List<CtModifiable> srcMod;
	List<CtModifiable> commonModifiable;

	// declaration
	String Access_Modifier;
	String Returned_Type;
	int Num_Parameters;
	boolean flagtemp = false;
	// metrics
	int LOC_Extracted_Method;

	// variable
	int Num_Variable;
	int Num_local;

	// Literal
	int Num_Literal;

	// Comments & Annotation
	int Num_Com;
	int Num_Annotation;
	int Num_AnnotationType;

	// Invocation
	int Num_Invocation;
	int Num_Executable;
	int Num_ExeRefExp;

	// Structure
	int Num_Loop;
	int Num_While;
	int Num_For;
	int Num_If;
	int Num_Conditional;
	int Num_Switch;

	// Access
	int Num_Var_Ac;
	int Num_Type_Ac;
	int Num_Field_Ac;
	int Num_Arr_Ac;
	int Num_Com_Var;
	int Num_Com_Var_Acc;
	int Num_Com_Field_Acc;
	int Num_Com_Invocation;
	int Num_Com_Type_Acc;
	int Num_Com_Typed_Ele;
	int Num_Com_Mod;
	/**
	 * Actions over all tree nodes (CtElements)
	 */
	private final List<Operation> allOperations;
	/**
	 * Actions over the changes roots.
	 */
	private final List<Operation> rootOperations;
	/**
	 * the mapping of this diff
	 */
	private final MappingStore _mappingsComp;
	/**
	 * Context of the spoon diff.
	 */
	private final TreeContext context;
	private int Num_Assert;
	private int Num_Assign;

	public DiffImpl(TreeContext context, ITree rootSpoonLeft, ITree rootSpoonRight,
			String Extracted_Mtd, String Src_Mtd) {
		final MappingStore mappingsComp = new MappingStore();

		final Matcher matcher = new CompositeMatchers.ClassicGumtree(rootSpoonLeft, rootSpoonRight,
				mappingsComp);
		matcher.match();

		final ActionGenerator actionGenerator = new ActionGenerator(rootSpoonLeft, rootSpoonRight,
				matcher.getMappings());
		actionGenerator.generate();

		final ActionClassifier actionClassifier = new ActionClassifier();
		this.allOperations = convertToSpoon(actionGenerator.getActions());
		this.rootOperations = convertToSpoon(
				actionClassifier.getRootActions(matcher.getMappingSet(), actionGenerator.getActions()));
		this._mappingsComp = mappingsComp;
		this.context = context;
		this.Name_Ext_Mtd = Extracted_Mtd;
		this.Name_Src_Mtd = Src_Mtd;
	}

	private List<Operation> convertToSpoon(List<Action> actions) {
		return actions.stream().map(action -> {
			if (action instanceof Insert) {
				return new InsertOperation((Insert) action);
			} else if (action instanceof Delete) {
				return new DeleteOperation((Delete) action);
			} else if (action instanceof Update) {
				return new UpdateOperation((Update) action);
			} else if (action instanceof Move) {
				return new MoveOperation((Move) action);
			} else {
				throw new IllegalArgumentException("Please support the new type " + action.getClass());
			}
		}).collect(Collectors.toList());
	}

	@Override
	public List<Operation> getAllOperations() {
		return Collections.unmodifiableList(allOperations);
	}

	@Override
	public List<Operation> getRootOperations() {
		return Collections.unmodifiableList(rootOperations);
	}

	@Override
	public List<Operation> getOperationChildren(Operation operationParent,
			List<Operation> rootOperations) {
		return rootOperations.stream() //
				.filter(operation -> operation.getNode().getParent().equals(operationParent)) //
				.collect(Collectors.toList());
	}

	@Override
	public CtElement changedNode() {
		if (rootOperations.size() != 1) {
			throw new IllegalArgumentException("Should have only one root action.");
		}
		return commonAncestor();
	}

	@Override
	public CtElement commonAncestor() {
		final List<CtElement> copy = new ArrayList<>();
		for (Operation operation : rootOperations) {
			CtElement el = operation.getNode();
			if (operation instanceof InsertOperation) {
				// we take the corresponding node in the source tree
				el = (CtElement) _mappingsComp.getSrc(operation.getAction().getNode().getParent())
						.getMetadata(SpoonGumTreeBuilder.SPOON_OBJECT);
			}
			copy.add(el);
		}
		while (copy.size() >= 2) {
			CtElement first = copy.remove(0);
			CtElement second = copy.remove(0);
			copy.add(commonAncestor(first, second));
		}
		return copy.get(0);
	}

	private CtElement commonAncestor(CtElement first, CtElement second) {
		while (first != null) {
			CtElement el = second;
			while (el != null) {
				if (first == el) {
					return first;
				}
				el = el.getParent();
			}
			first = first.getParent();
		}
		return null;
	}

	@Override
	public CtElement changedNode(Class<? extends Operation> operationWanted) {
		final Optional<Operation> firstNode = rootOperations.stream() //
				.filter(operation -> operationWanted.isAssignableFrom(operation.getClass())) //
				.findFirst();
		if (firstNode.isPresent()) {
			return firstNode.get().getNode();
		}
		throw new NoSuchElementException();
	}

	@Override
	public boolean containsOperation(OperationKind kind, String nodeKind) {
		return rootOperations.stream() //
				.anyMatch(operation -> operation.getAction().getClass().getSimpleName().equals(kind.name()) //
						&& context.getTypeLabel(operation.getAction().getNode()).equals(nodeKind));
	}

	@Override
	public boolean containsOperation(OperationKind kind, String nodeKind, String nodeLabel) {
		return containsOperations(getRootOperations(), kind, nodeKind, nodeLabel);
	}

	@Override
	public boolean containsOperations(List<Operation> operations, OperationKind kind, String nodeKind,
			String nodeLabel) {
		return operations.stream()
				.anyMatch(operation -> operation.getAction().getClass().getSimpleName().equals(kind.name()) //
						&& context.getTypeLabel(operation.getAction().getNode()).equals(nodeKind) //
						&& operation.getAction().getNode().getLabel().equals(nodeLabel));
	}

	@Override
	public void debugInformation() {
		System.err.println(toDebugString());
	}

	private String toDebugString() {
		String result = "";
		for (Operation operation : rootOperations) {
			ITree node = operation.getAction().getNode();
			final CtElement nodeElement = operation.getNode();
			String label = "\"" + node.getLabel() + "\"";
			if (operation instanceof UpdateOperation) {
				label += " to \"" + ((Update) operation.getAction()).getValue() + "\"";
			}
			String nodeType = "CtfakenodeImpl";
			if (nodeElement != null) {
				nodeType = nodeElement.getClass().getSimpleName();
				nodeType = nodeType.substring(2, nodeType.length() - 4);
			}
			result += "\"" + operation.getAction().getClass().getSimpleName() + "\", \"" + nodeType
					+ "\", " + label + " (size: " + node.getDescendants().size() + ")" + node.toTreeString();
		}
		System.out.println(result);
		return result;
	}

	// 去重
	public <T> List<T> getNewList(List<T> li) {
		List<T> list = new ArrayList<T>();
		for (int i = 0; i < li.size(); i++) {
			T str = li.get(i); // 获取传入集合对象的每一个元素
			if (!list.contains(str)) { // 查看新集合中是否有指定的元素，如果没有则加入
				list.add(str);
			}
		}
		return list; // 返回集合
	}

	public void print_after() throws IOException {
		File file_after = new File("after_method");
		file_after.createNewFile();
		FileWriter fileWriter = new FileWriter(file_after);
		fileWriter.write("------------------Extracted method---------------------" + "\n" + "\n"
				+ extracted_Method.toString() + "\n" + "\n"
				+ "-------------------Methods who call it--------------------" + "\n" + "\n");
		callMethod = getNewList(callMethod); // 去重
		int size = callMethod.size();
		System.out.println("--------------call method----------------" + callMethod.size());
		for (int i = 0; i < size; i++) {
			fileWriter.write(callMethod.get(i).toString() + "\n" + "\n");
		}
		fileWriter.write("--------------------------end------------------------------" + "\n");
		fileWriter.close();
	}

	public void print_before() throws IOException {
		int size3 = deleteStuff.size();
		int t;
		double sim1, sim2;
		sim1 = 0;
		sim2 = 0;
		CtElement tempEl;
		for (t = 0; t < size3; t++) {
			tempEl = deleteStuff.get(t);
			sim2 = sim(tempEl.toString(), extracted_Method.getBody().toString());
			System.out.println(
					"the code is: " + tempEl.toString() + "the similarity of this stuff is: " + sim2);
			if (sim2 > sim1) {
				deleted = tempEl;
				sim1 = sim2;
			}
		}
		if (sim(deleted.toString(), extracted_Method.getBody().toString()) < 0.4) {
			deleted = extracted_Method.getBody();
			System.out.println("use extracted method directly");
		}
		File file_before = new File("before_method");
		file_before.createNewFile();
		FileWriter fileWriter2 = new FileWriter(file_before);
		fileWriter2.write("-----------------------Extracted Part---------------------" + "\n" + "\n"
				+ deleted.toString() + "\n" + "\n");
		fileWriter2.write(
				"--------------------------Source Methods------------------------------" + "\n" + "\n");
		sourceMethod = getNewList(sourceMethod); // 去重
		int size = sourceMethod.size();
		for (int i = 0; i < size; i++) {
			fileWriter2.write(sourceMethod.get(i).toString() + "\n" + "\n");
		}
		fileWriter2.write("--------------------------end-----------------------------" + "\n" + "\n");
		fileWriter2.close();
	}

	@Override
	public String toString() {
		if (rootOperations.size() == 0) {
			return "no AST change";
		}
		final StringBuilder stringBuilder = new StringBuilder();
		final CtElement ctElement = commonAncestor();
		String temp = null;
		for (Operation operation : rootOperations) {
			try {
				temp = toStringAction(operation.getAction());
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			if (temp.length() > 0) {
				stringBuilder.append(temp);
				if (operation.getNode().equals(ctElement) && operation instanceof InsertOperation) {
					break;
				}
			}
		}
		try {
			print_after();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		try {
			print_before();
		} catch (IOException e) {
			e.printStackTrace();
		}
		print_file();
		return stringBuilder.toString();
	}

	private static int min(int one, int two, int three) {
		int min = one;
		if (two < min) {
			min = two;
		}
		if (three < min) {
			min = three;
		}
		return min;
	}

	public static int ld(String str1, String str2) {
		int d[][]; // 矩阵
		int n = str1.length();
		int m = str2.length();
		int i; // 遍历str1的
		int j; // 遍历str2的
		char ch1; // str1的
		char ch2; // str2的
		int temp; // 记录相同字符,在某个矩阵位置值的增量,不是0就是1
		if (n == 0) {
			return m;
		}
		if (m == 0) {
			return n;
		}
		d = new int[n + 1][m + 1];
		for (i = 0; i <= n; i++) { // 初始化第一列
			d[i][0] = i;
		}
		for (j = 0; j <= m; j++) { // 初始化第一行
			d[0][j] = j;
		}
		for (i = 1; i <= n; i++) { // 遍历str1
			ch1 = str1.charAt(i - 1);
			for (j = 1; j <= m; j++) {
				ch2 = str2.charAt(j - 1);
				if (ch1 == ch2) {
					temp = 0;
				} else {
					temp = 1;
				}
				d[i][j] = min(d[i - 1][j] + 1, d[i][j - 1] + 1, d[i - 1][j - 1] + temp);
			}
		}
		return d[n][m];
	}

	public static double sim(String str1, String str2) {
		int ld = ld(str1, str2);
		return 1 - (double) ld / Math.max(str1.length(), str2.length());
	}

	public void print_file() {
		// ---------------------------------------------Print
		File file = new File("file.csv");
		// File file = new File("file.csv");
		CSVFormat format = null;
		if (file.exists()) {
			format = CSVFormat.DEFAULT.withHeader("Src_Modifiers", "Src_Num_Parameters", "Src_LOC",
					"Src_Num_local", "Src_Num_Literal", "Src_Num_Invocation", "Src_Num_Loop", "Src_Num_While",
					"Src_Num_For", "Src_Num_If", "Src_Num_Conditional", "Src_Num_Switch", "Src_Num_Var_Ac",
					"Src_Num_Field_Ac", "Src_Num_Arr_Ac", "Src_Num_Assert", "Src_Num_Assign",
					"LOC_Extracted_Method", "Num_local", "Num_Literal", "Num_Invocation", "Num_Loop",
					"Num_While", "Num_For", "Num_If", "Num_Conditional", "Num_Switch", "Num_Var_Ac",
					"Num_Field_Ac", "Num_Arr_Ac", "Num_Assert", "Num_Assign", "commonVariableAccess",
					"commonFieldAccess", "commonInvocation", "commonTypeAccess", "commonTypedElement",
					"commonModifiable").withSkipHeaderRecord();
		} else {
			format = CSVFormat.DEFAULT.withHeader("Src_Modifiers", "Src_Num_Parameters", "Src_LOC",
					"Src_Num_local", "Src_Num_Literal", "Src_Num_Invocation", "Src_Num_Loop", "Src_Num_While",
					"Src_Num_For", "Src_Num_If", "Src_Num_Conditional", "Src_Num_Switch", "Src_Num_Var_Ac",
					"Src_Num_Field_Ac", "Src_Num_Arr_Ac", "Src_Num_Assert", "Src_Num_Assign",
					"LOC_Extracted_Method", "Num_local", "Num_Literal", "Num_Invocation", "Num_Loop",
					"Num_While", "Num_For", "Num_If", "Num_Conditional", "Num_Switch", "Num_Var_Ac",
					"Num_Field_Ac", "Num_Arr_Ac", "Num_Assert", "Num_Assign", "commonVariableAccess",
					"commonFieldAccess", "commonInvocation", "commonTypeAccess", "commonTypedElement",
					"commonModifiable");
		}

		try (Writer out = new FileWriter("file.csv", true);
				CSVPrinter printer = new CSVPrinter(out, format)) {
			System.out.println("--------------source method----------------" + sourceMethod.size());
			for (int w = 0; w < sourceMethod.size(); w++) {
				CtMethod m = (CtMethod) sourceMethod.get(w);
				String Name_Src_Method = m.getSimpleName().toString();
				String Src_Returned_Type = m.getType().getSimpleName().toString();
				String ttt = m.getBody().getElements(new TypeFilter(CtComment.class)).toString();
				int Src_Num_Parameters = m.getParameters().size();
				int Src_LOC = m.getBody().getStatements().size();
				int Src_Num_Variable = m.getBody().getElements(new TypeFilter(CtVariable.class)).size();
				int Src_Num_local = m.getBody().getElements(new TypeFilter(CtLocalVariable.class)).size();
				int Src_Num_Literal = m.getBody().getElements(new TypeFilter(CtLiteral.class)).size();
				int Src_Num_Assert = m.getBody().getElements(new TypeFilter(CtAssert.class)).size();
				int Src_Num_Com = m.getBody().getElements(new TypeFilter(CtComment.class)).size();
				int Src_Num_Annotation = m.getBody().getElements(new TypeFilter(CtAnnotation.class)).size();
				int Src_Num_Invocation = m.getBody().getElements(new TypeFilter(CtInvocation.class)).size();
				int Src_Num_Executable = m.getBody().getElements(new TypeFilter(CtExecutable.class)).size();
				int Src_Num_ExeRefExp = m.getBody()
						.getElements(new TypeFilter(CtExecutableReferenceExpression.class)).size();
				int Src_Num_Loop = m.getBody().getElements(new TypeFilter(CtLoop.class)).size();
				int Src_Num_While = m.getBody().getElements(new TypeFilter(CtWhile.class)).size();
				int Src_Num_For = m.getBody().getElements(new TypeFilter(CtFor.class)).size();
				int Src_Num_If = m.getBody().getElements(new TypeFilter(CtIf.class)).size();
				int Src_Num_Conditional = m.getBody().getElements(new TypeFilter(CtConditional.class))
						.size();
				int Src_Num_Switch = m.getBody().getElements(new TypeFilter(CtSwitch.class)).size();
				int Src_Num_Var_Ac = m.getBody().getElements(new TypeFilter(CtVariableAccess.class)).size();
				int Src_Num_Type_Ac = m.getBody().getElements(new TypeFilter(CtTypeAccess.class)).size();
				int Src_Num_Field_Ac = m.getBody().getElements(new TypeFilter(CtFieldAccess.class)).size();
				int Src_Num_Arr_Ac = m.getBody().getElements(new TypeFilter(CtArrayAccess.class)).size();
				int Src_Num_Assign = m.getBody().getElements(new TypeFilter(CtAssignment.class)).size();
				String Src_Modifiers = m.getModifiers().toString();

				// metrics
				LOC_Extracted_Method = deleted.getElements(new TypeFilter(CtStatement.class)).size();

				// variable
				Num_Variable = deleted.getElements(new TypeFilter(CtVariable.class)).size();
				Num_local = deleted.getElements(new TypeFilter(CtLocalVariable.class)).size();

				// Literal
				Num_Literal = deleted.getElements(new TypeFilter(CtLiteral.class)).size();

				// Comments & Annotation
				Num_Com = deleted.getElements(new TypeFilter(CtComment.class)).size();
				Num_Annotation = deleted.getElements(new TypeFilter(CtAnnotation.class)).size();
				Num_AnnotationType = deleted.getElements(new TypeFilter(CtAnnotationType.class)).size();

				// Invocation
				Num_Invocation = deleted.getElements(new TypeFilter(CtInvocation.class)).size();
				Num_Executable = deleted.getElements(new TypeFilter(CtExecutable.class)).size();
				Num_ExeRefExp = deleted.getElements(new TypeFilter(CtExecutableReferenceExpression.class))
						.size();

				// Structure
				Num_Loop = deleted.getElements(new TypeFilter(CtLoop.class)).size();
				Num_While = deleted.getElements(new TypeFilter(CtWhile.class)).size();
				Num_For = deleted.getElements(new TypeFilter(CtFor.class)).size();
				Num_If = deleted.getElements(new TypeFilter(CtIf.class)).size();
				Num_Conditional = deleted.getElements(new TypeFilter(CtConditional.class)).size();
				Num_Switch = deleted.getElements(new TypeFilter(CtSwitch.class)).size();

				// Access
				Num_Var_Ac = deleted.getElements(new TypeFilter(CtVariableAccess.class)).size();
				Num_Type_Ac = deleted.getElements(new TypeFilter(CtTypeAccess.class)).size();
				Num_Field_Ac = deleted.getElements(new TypeFilter(CtFieldAccess.class)).size();
				Num_Arr_Ac = deleted.getElements(new TypeFilter(CtArrayAccess.class)).size();
				Num_Assert = deleted.getElements(new TypeFilter(CtAssert.class)).size();
				Num_Assign = deleted.getElements(new TypeFilter(CtAssignment.class)).size();

				// F3 common variable declaration between F2 and the rest (including repeated ones)
				deletedVariable = new ArrayList<CtVariable>(
						deleted.getElements(new TypeFilter(CtVariable.class)));
				srcVariable = new ArrayList<CtVariable>(m.getElements(new TypeFilter(CtVariable.class)));
				commonVariable = new ArrayList<CtVariable>(getCommon(deletedVariable, srcVariable));
				Num_Com_Var = commonVariable.size();

				// F3 common variable access between F2 and the rest (including repeated ones)
				delVarAcc = new ArrayList<CtVariableAccess>(
						deleted.getElements(new TypeFilter(CtVariableAccess.class)));
				srcVarAcc = new ArrayList<CtVariableAccess>(
						m.getElements(new TypeFilter(CtVariableAccess.class)));
				commonVariableAccess = new ArrayList<CtVariableAccess>(getCommon(delVarAcc, srcVarAcc));
				commonVariableAccess = getNewList(commonVariableAccess);
				Num_Com_Var_Acc = commonVariableAccess.size();

				// F3 common field access between F2 and the rest (including repeated ones)
				delFieldAcc = new ArrayList<CtFieldAccess>(
						deleted.getElements(new TypeFilter(CtFieldAccess.class)));
				srcFieldAcc = new ArrayList<CtFieldAccess>(
						m.getElements(new TypeFilter(CtFieldAccess.class)));
				commonFieldAccess = new ArrayList<CtFieldAccess>(getCommon(delFieldAcc, srcFieldAcc));
				commonFieldAccess = getNewList(commonFieldAccess);
				Num_Com_Field_Acc = commonFieldAccess.size();

				// F3 common invocation between F2 and the rest (including repeated ones)
				delInvo = new ArrayList<CtInvocation>(
						deleted.getElements(new TypeFilter(CtInvocation.class)));
				srcInvo = new ArrayList<CtInvocation>(m.getElements(new TypeFilter(CtInvocation.class)));
				commonInvo = new ArrayList<CtInvocation>(getCommon(delInvo, srcInvo));
				commonInvo = getNewList(commonInvo);
				Num_Com_Invocation = commonInvo.size();

				// F3 common type access between F2 and the rest (including repeated ones)
				delTypeAcc = new ArrayList<CtTypeAccess>(
						deleted.getElements(new TypeFilter(CtTypeAccess.class)));
				srcTypeAcc = new ArrayList<CtTypeAccess>(m.getElements(new TypeFilter(CtTypeAccess.class)));
				commonTypeAccess = new ArrayList<CtTypeAccess>(getCommon(delTypeAcc, srcTypeAcc));
				commonTypeAccess = getNewList(commonTypeAccess);
				Num_Com_Type_Acc = commonTypeAccess.size();

				// F3 common typed element between F2 and the rest (including repeated ones)
				delTypedEle = new ArrayList<CtTypedElement>(
						deleted.getElements(new TypeFilter(CtTypedElement.class)));
				srcTypedEle = new ArrayList<CtTypedElement>(
						m.getElements(new TypeFilter(CtTypedElement.class)));
				commonTypedElement = new ArrayList<CtTypedElement>(getCommon(delTypedEle, srcTypedEle));
				commonTypedElement = getNewList(commonTypedElement);
				Num_Com_Typed_Ele = commonTypedElement.size();

				// F3 common type access between F2 and the rest (including repeated ones)
				delMod = new ArrayList<CtModifiable>(
						deleted.getElements(new TypeFilter(CtModifiable.class)));
				srcMod = new ArrayList<CtModifiable>(m.getElements(new TypeFilter(CtModifiable.class)));
				commonModifiable = new ArrayList<CtModifiable>(getCommon(delMod, srcMod));
				commonModifiable = getNewList(commonModifiable);
				Num_Com_Mod = commonModifiable.size();

				printer.printRecord(Src_Modifiers, Src_Num_Parameters, Src_LOC, Src_Num_local,
						Src_Num_Literal, Src_Num_Invocation, Src_Num_Loop, Src_Num_While, Src_Num_For,
						Src_Num_If, Src_Num_Conditional, Src_Num_Switch, Src_Num_Var_Ac, Src_Num_Field_Ac,
						Src_Num_Arr_Ac, Src_Num_Assert, Src_Num_Assign, LOC_Extracted_Method, Num_local,
						Num_Literal, Num_Invocation, Num_Loop, Num_While, Num_For, Num_If, Num_Conditional,
						Num_Switch, Num_Var_Ac, Num_Field_Ac, Num_Arr_Ac, Num_Assert, Num_Assign,
						Num_Com_Var_Acc, Num_Com_Field_Acc, Num_Com_Invocation, Num_Com_Type_Acc,
						Num_Com_Typed_Ele, Num_Com_Mod);
				printer.flush();
			}
			printer.close();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	private <T> List<T> getCommon(List<T> deletedStuff, List<T> srcStuff) {
		List<T> temp1 = new ArrayList<T>(deletedStuff);
		List<T> temp2 = new ArrayList<T>(srcStuff);
		temp2.retainAll(temp1);
		int i, j;
		T t;
		for (i = 0; i < temp2.size(); i++) {
			t = temp2.get(i);
			if (temp1.contains(t)) {
				temp2.remove(i);
				i--;
				temp1.remove(temp1.indexOf(t));
			}
		}
		return temp2;
	}

	private String toStringAction(Action action) throws IOException {
		String newline = System.getProperty("line.separator");
		StringBuilder stringBuilder = new StringBuilder();
		CtElement element = (CtElement) action.getNode().getMetadata(SpoonGumTreeBuilder.SPOON_OBJECT);
		if (element != null) {
			// element != Try
			if (!((element.getClass().getSimpleName().substring(2,
					element.getClass().getSimpleName().length() - 4)).equalsIgnoreCase("Try"))) {
				// action name
				stringBuilder.append(action.getClass().getSimpleName());
				System.out.println("action: " + action.getClass().getSimpleName());

				// node type
				String nodeType = element.getClass().getSimpleName();
				nodeType = nodeType.substring(2, nodeType.length() - 4);
				System.out.println("nodeType: " + nodeType + "");
				stringBuilder.append(" ").append(nodeType);

				// action position
				CtElement parent = element;
				while (parent.getParent() != null && !(parent.getParent() instanceof CtPackage)) {
					parent = parent.getParent();
				}
				String position = " at ";
				if (parent instanceof CtType) {
					position += ((CtType) parent).getQualifiedName();
				}
				if (element.getPosition() != null) {
					position += ":" + element.getPosition().getLine();
				}
				if (action instanceof Insert) {
					if ((element instanceof CtMethod)) {
						CtMethod te2 = (CtMethod) element;
						if (te2.getSimpleName().toString().equals(Name_Src_Mtd)
								&& element.toString().contains(Name_Ext_Mtd)) {
							callMethod.add(te2);
						} else if (te2.getSimpleName().toString().equals(Name_Ext_Mtd) && flagtemp == false) {
							flagtemp = true;
							System.out.println("--------------------A new method is inserted!");
							extracted_Method = te2;
						}
					} else if (element.toString().contains(Name_Ext_Mtd)
							&& !nodeType.equalsIgnoreCase("Constructor")) {
						CtElement callIt = element;
						while (!(callIt instanceof CtMethod) && !(callIt instanceof CtConstructor)
								&& !(callIt instanceof CtClass)) {
							callIt = callIt.getParent();
						}
						if (callIt instanceof CtMethod) {
							CtMethod m = (CtMethod) callIt;
							if (m.getSimpleName().toString().equals(Name_Src_Mtd)) {
								callMethod.add((CtMethod) callIt);
							}
						}
					}
				}
				if (action instanceof Delete) {
					if (!(element instanceof CtMethod)) {
						CtElement callIt = element;
						while (!(callIt instanceof CtMethod) && !(callIt instanceof CtConstructor)
								&& !(callIt instanceof CtClass)) {
							callIt = callIt.getParent();
						}
						if (callIt instanceof CtMethod) {
							CtMethod src_temp = (CtMethod) callIt;
							if (src_temp.getSimpleName().toString().equals(Name_Src_Mtd)) {
								deleteStuff.add(element);
								sourceMethod.add(src_temp);
							}
						}
					}
				}
				if (action instanceof Move) {
					if (!nodeType.equalsIgnoreCase("ThisAccess") && !nodeType.equalsIgnoreCase("TypeAccess")
							&& !nodeType.equalsIgnoreCase("Constructor")) {
						if (!(element instanceof CtMethod)) {
							CtElement callIt = element;
							while (!(callIt instanceof CtMethod) && !(callIt instanceof CtConstructor)
									&& !(callIt instanceof CtClass)) {
								callIt = callIt.getParent();
							}
							if (callIt instanceof CtMethod) {
								CtMethod temp_method = (CtMethod) callIt;
								if (temp_method.getSimpleName().toString().equals(Name_Src_Mtd)) {
									deleteStuff.add(element);
									sourceMethod.add(temp_method);
								}
							}
						}
						CtElement elementDest = (CtElement) action.getNode()
								.getMetadata(SpoonGumTreeBuilder.SPOON_OBJECT_DEST);
						position = " from " + element.getParent(CtClass.class).getQualifiedName() + ":"
								+ element.getPosition().getLine();
						position += " to " + elementDest.getParent(CtClass.class).getQualifiedName() + ":"
								+ elementDest.getPosition().getLine();
					}
				}
				stringBuilder.append(position).append(newline);

				String label = element.toString();
				if (action instanceof Update) {
					CtElement callIt = element;
					while (!(callIt instanceof CtMethod) && !(callIt instanceof CtConstructor)
							&& !(callIt instanceof CtClass)) {
						callIt = callIt.getParent();
					}
					if (callIt instanceof CtMethod) {
						CtMethod temp_method = (CtMethod) callIt;
						if (temp_method.getSimpleName().toString().equals(Name_Src_Mtd)) {
							sourceMethod.add(temp_method);
						}
					}
					CtElement elementDest = (CtElement) action.getNode()
							.getMetadata(SpoonGumTreeBuilder.SPOON_OBJECT_DEST);
					if (elementDest instanceof CtMethod) {
						CtMethod temp_dest = (CtMethod) elementDest;
						if (flagtemp == false && temp_dest.getSimpleName().toString().equals(Name_Ext_Mtd)) {
							flagtemp = true;
							extracted_Method = temp_dest;
							System.out.println("--------------------A new method is updated !");
						} else if (temp_dest.getSimpleName().equals(Name_Src_Mtd)
								&& temp_dest.toString().contains(Name_Ext_Mtd)) {
							callMethod.add(temp_dest);
						}
					} else if (!nodeType.equalsIgnoreCase("Constructor")
							&& elementDest.toString().contains(Name_Ext_Mtd)) {
						CtElement callIt1 = elementDest;
						while (!(callIt1 instanceof CtMethod) && !(callIt1 instanceof CtConstructor)
								&& !(callIt1 instanceof CtClass)) {
							callIt1 = callIt1.getParent();
						}
						if (callIt1 instanceof CtMethod) {
							callMethod.add((CtMethod) callIt1);
						}
					}
					label += " to " + elementDest.toString();
				}
				String[] split = label.split(newline);
				for (String s : split) {
					stringBuilder.append("\t").append(s).append(newline);
				}
			}
		}
		return stringBuilder.toString();
	}
}
