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
import spoon.reflect.code.CtAssert;
import spoon.reflect.code.CtAssignment;
import spoon.reflect.code.CtBlock;
import spoon.reflect.code.CtConditional;
import spoon.reflect.code.CtFieldAccess;
import spoon.reflect.code.CtIf;
import spoon.reflect.code.CtInvocation;
import spoon.reflect.code.CtLiteral;
import spoon.reflect.code.CtLocalVariable;
import spoon.reflect.code.CtSwitch;
import spoon.reflect.code.CtTypeAccess;
import spoon.reflect.code.CtVariableAccess;
import spoon.reflect.declaration.CtClass;
import spoon.reflect.declaration.CtConstructor;
import spoon.reflect.declaration.CtElement;
import spoon.reflect.declaration.CtMethod;
import spoon.reflect.declaration.CtModifiable;
import spoon.reflect.declaration.CtPackage;
import spoon.reflect.declaration.CtParameter;
import spoon.reflect.declaration.CtType;
import spoon.reflect.declaration.CtTypedElement;
import spoon.reflect.declaration.CtVariable;
import spoon.reflect.visitor.filter.TypeFilter;
import spoon.support.reflect.reference.CtPackageReferenceImpl;

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

	// Package only used in the extracted code
	CtPackageReferenceImpl package_most_used;
	CtVariable variable_most_used;
	CtVariableAccess variable_access_most_used;
	CtFieldAccess field_access_most_used;
	CtInvocation invocation_most_used;
	CtTypeAccess type_access_most_used;
	CtTypedElement typed_ele_most_used;
	CtModifiable modifiable_most_used;

	// List<CtElement> callMethod = new ArrayList<CtElement>(); // after version里的source method
	// List<CtElement> sourceMethod = new ArrayList<CtElement>(); // before version里的source method
	List<CtElement> deleteStuff = new ArrayList<CtElement>();
	CtElement extracted_Method; // extracted method
	CtBlock extracted_Code;
	CtElement call_Method;
	CtElement src_Method;
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
	boolean noASTchange = false;
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
	private int Num_Assign;

	public DiffImpl(TreeContext context, ITree rootSpoonLeft, ITree rootSpoonRight, String Extracted_Mtd,
			String Src_Mtd, int params_E, int params_S) {
		boolean flag1, flag2, flag3;
		flag1 = flag2 = flag3 = false;
		// get the new extracted method and the call method
		CtElement all_after = (CtElement) rootSpoonRight.getChild(0).getMetadata((SpoonGumTreeBuilder.SPOON_OBJECT));
		List<CtMethod> methods_after = all_after.getElements(new TypeFilter(CtMethod.class));
		for (int i = 0; i < methods_after.size(); i++) {
			CtMethod aMethod = methods_after.get(i);
			String aName = aMethod.getSimpleName().toString();
			if (aName.equals(Extracted_Mtd) && aMethod.getParameters().size() == params_E
					&& !aMethod.getBody().toString().contains((Extracted_Mtd + "("))) {
				extracted_Method = aMethod.clone();
				flag1 = true;
			} else if (aName.equals(Src_Mtd) && aMethod.getParameters().size() == params_S
					&& aMethod.getBody().toString().contains((Extracted_Mtd + "("))) {
				call_Method = aMethod.clone();
				flag2 = true;
			}
		}
		if (flag1 == false || flag2 == false) {
			List<CtConstructor> con_after = all_after.getElements(new TypeFilter(CtConstructor.class));
			System.out.println("cannot find extracted_Method or call method");
			for (int j = 0; j < con_after.size(); j++) {
				CtConstructor aCon = con_after.get(j);
				String aName = aCon.getSimpleName().toString();
				if (aName.equals(Extracted_Mtd) && aCon.getParameters().size() == params_E
						&& !aCon.getBody().toString().contains((Extracted_Mtd + "("))) {
					flag1 = true;
					extracted_Method = aCon.clone();
				} else if (aName.equals(Src_Mtd) && aCon.getParameters().size() == params_S
						&& aCon.getBody().toString().contains((Extracted_Mtd + "("))) {
					flag2 = true;
					call_Method = aCon.clone();
				}
			}
		}
		// get the source method
		CtElement all_before = (CtElement) rootSpoonLeft.getChild(0).getMetadata((SpoonGumTreeBuilder.SPOON_OBJECT));
		List<CtMethod> methods_before = all_before.getElements(new TypeFilter(CtMethod.class));
		for (int i = 0; i < methods_before.size(); i++) {
			CtMethod aMethod = methods_before.get(i);
			String aName = aMethod.getSimpleName().toString();
			if (aName.equals(Src_Mtd) && aMethod.getParameters().size() == params_S) {
				src_Method = aMethod.clone();
				flag3 = true;
				break;
			}
		}
		if (flag3 == false) {
			List<CtConstructor> con_before = all_before.getElements(new TypeFilter(CtConstructor.class));
			for (int j = 0; j < con_before.size(); j++) {
				CtConstructor aCon = con_before.get(j);
				String aName = aCon.getSimpleName().toString();
				if (aName.equals(Src_Mtd) && aCon.getParameters().size() == params_S) {
					src_Method = aCon.clone();
					flag3 = true;
				}
			}
		}
		if (flag1 == false) {
			System.out.println(Extracted_Mtd + ": cannot find extracted_Method method");
		}
		if (flag2 == false) {
			System.out.println(Extracted_Mtd + ": cannot find call_Method method");
		}
		if (flag3 == false) {
			System.out.println(Extracted_Mtd + ": cannot find src_Method method");
		}
		final MappingStore mappingsComp = new MappingStore();

		final Matcher matcher = new CompositeMatchers.ClassicGumtree(rootSpoonLeft, rootSpoonRight, mappingsComp);
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
		if (extracted_Method instanceof CtMethod) {
			extracted_Code = ((CtMethod) extracted_Method).getBody();
		} else if (extracted_Method instanceof CtConstructor) {
			extracted_Code = ((CtConstructor) extracted_Method).getBody();
		}
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
	public List<Operation> getOperationChildren(Operation operationParent, List<Operation> rootOperations) {
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
			result += "\"" + operation.getAction().getClass().getSimpleName() + "\", \"" + nodeType + "\", " + label
					+ " (size: " + node.getDescendants().size() + ")" + node.toTreeString();
		}
		System.out.println(result);
		return result;
	}

	// 去重
	public <T> List<T> getNewList(List<T> li) {
		li = filterNull(li);
		List<T> list = new ArrayList<T>();
		for (int i = 0; i < li.size(); i++) {
			T str = li.get(i); // 获取传入集合对象的每一个元素
			if (!list.contains(str)) { // 查看新集合中是否有指定的元素，如果没有则加入
				list.add(str);
			}
		}
		return list; // 返回集合
	}

	public static <T> int contains2(List<T> src, T str) {
		for (T var : src) {
			if (var.toString().equals(str.toString())) {
				return src.indexOf(var);
			}
		}
		return (-1);
	}

	public static <T> List<T> filterNull(List<T> list) {
		for (int i = 0; i < list.size(); i++) {
			if (list.get(i).toString().equals("")) {
				list.remove(i);
				i--;
			}
		}
		return list;
	}

	public static <T> List<T> minusList(List<T> src, List<T> deleted) {
		List<T> list = new ArrayList<T>(src);
		System.out.println("src list: " + src.toString());
		System.out.println("del list: " + deleted.toString());
		List<T> list2 = new ArrayList<T>(deleted);
		for (int i = 0; i < list2.size(); i++) {
			T str = list2.get(i); // 获取传入集合对象的每一个元素
			int index = contains2(list, str);
			if (index != -1) { // 查看新集合中是否有指定的元素，如果没有则加入
				list.remove(index);
			}
		}
		list = filterNull(list);
		System.out.println("remain list: " + list.toString());
		return list; // 返回集合
	}

	public void print_after() throws IOException {
		File file_after = new File("after_method");
		file_after.createNewFile();
		FileWriter fileWriter = new FileWriter(file_after);
		fileWriter.write(
				"------------------Extracted method---------------------" + "\n" + "\n" + extracted_Method.toString()
						+ "\n" + "\n" + "-------------------Methods who call it--------------------" + "\n" + "\n"
						+ call_Method.toString() + "\n" + "\n");
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
			sim2 = sim(tempEl.toString(), extracted_Code.toString());
			System.out.println("the code is: " + tempEl.toString() + "the similarity of this stuff is: " + sim2);
			if (sim2 > sim1) {
				deleted = tempEl;
				sim1 = sim2;
			}
		}
		if (size3 == 0 || sim(deleted.toString(), extracted_Code.toString()) < 0.6) {
			deleted = extracted_Code;
			System.out.println("use extracted method directly");
		}
		File file_before = new File("before_method");
		file_before.createNewFile();
		FileWriter fileWriter2 = new FileWriter(file_before);
		fileWriter2.write("-----------------------Extracted Part---------------------" + "\n" + "\n"
				+ deleted.toString() + "\n" + "\n");
		fileWriter2.write("--------------------------Source Methods------------------------------" + "\n" + "\n");
		fileWriter2.write(src_Method.toString() + "\n" + "\n");
		fileWriter2.write("--------------------------end-----------------------------" + "\n" + "\n");
		fileWriter2.close();
	}

	@Override
	public String toString() {
		String result;
		if (rootOperations.size() == 0) {
			CtBlock src_blk;
			if (src_Method instanceof CtMethod) {
				src_blk = ((CtMethod) call_Method).getBody().clone();
				src_blk.addStatement(extracted_Code);
				CtMethod source = (CtMethod) call_Method.clone();
				source.setBody(src_blk);
				src_Method = source;
			} else if (src_Method instanceof CtConstructor) {
				src_blk = ((CtConstructor) call_Method).getBody().clone();
				src_blk.addStatement(extracted_Code);
				CtConstructor source = (CtConstructor) call_Method.clone();
				source.setBody(src_blk);
				src_Method = source;
			}
			result = "no AST change";
		} else {
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
			result = stringBuilder.toString();
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
		return result;
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

	public static List<CtLiteral> filterNum(List<CtLiteral> con_literal) {
		for (int i = 0; i < con_literal.size(); i++) {
			if (!con_literal.get(i).toString().contains("\"")) {
				con_literal.remove(i);
				i--;
			}
		}
		return con_literal;
	}

	public void print_file() {
		// ---------------------------------------------Print
		File file = new File("con_pos1.csv");
		CSVFormat format = null;
		if (file.exists()) {
			format = CSVFormat.DEFAULT
					.withHeader("Name_Ext_Mtd", "Con_LOC", "CON_LOCAL", "CON_LITERAL", "CON_INVOCATION", "CON_IF",
							"CON_CONDITIONAL", "CON_SWITCH", "CON_VAR_ACC", "CON_TYPE_ACC", "CON_FIELD_ACC",
							"CON_ASSERT", "CON_ASSIGN", "CON_TYPED_ELE", "CON_PACKAGE", "LOC_Extracted_Method",
							"Num_Variable", "Num_local", "Num_Literal", "Num_Invocation", "Num_If", "Num_Conditional",
							"Num_Switch", "Num_Var_Ac", "Num_Type_Ac", "Num_Field_Ac", "Num_Assign", "Num_Typed_Ele",
							"Num_Package", "ratio_LOC", "Ratio_Variable_Access", "Ratio_Variable_Access2",
							"Ratio_Field_Access", "Ratio_Field_Access2", "Ratio_Type_Access", "Ratio_Type_Access2",
							"Ratio_Typed_Ele", "Ratio_Typed_Ele2", "Ratio_Package", "Ratio_Package2", "Coh_Pacakge")
					.withSkipHeaderRecord();
		} else {
			format = CSVFormat.DEFAULT.withHeader("Name_Ext_Mtd", "Con_LOC", "CON_LOCAL", "CON_LITERAL",
					"CON_INVOCATION", "CON_IF", "CON_CONDITIONAL", "CON_SWITCH", "CON_VAR_ACC", "CON_TYPE_ACC",
					"CON_FIELD_ACC", "CON_ASSERT", "CON_ASSIGN", "CON_TYPED_ELE", "CON_PACKAGE", "LOC_Extracted_Method",
					"Num_Variable", "Num_local", "Num_Literal", "Num_Invocation", "Num_If", "Num_Conditional",
					"Num_Switch", "Num_Var_Ac", "Num_Type_Ac", "Num_Field_Ac", "Num_Assign", "Num_Typed_Ele",
					"Num_Package", "ratio_LOC", "Ratio_Variable_Access", "Ratio_Variable_Access2", "Ratio_Field_Access",
					"Ratio_Field_Access2", "Ratio_Type_Access", "Ratio_Type_Access2", "Ratio_Typed_Ele",
					"Ratio_Typed_Ele2", "Ratio_Package", "Ratio_Package2", "Coh_Pacakge");
		}
		try (Writer out = new FileWriter("con_pos1.csv", true); CSVPrinter printer = new CSVPrinter(out, format)) {
			// get the body of source method: blk
			CtBlock blk = null;
			if (src_Method instanceof CtMethod) {
				CtMethod m = (CtMethod) src_Method;
				blk = m.getBody();
			} else if (src_Method instanceof CtConstructor) {
				CtConstructor constr = (CtConstructor) src_Method;
				blk = constr.getBody();
			}

			// get the body of Call Method(the after version of source method) : blk2
			CtBlock blk2 = null;
			if (call_Method instanceof CtMethod) {
				CtMethod srcMe = (CtMethod) call_Method;
				blk2 = srcMe.getBody();
			} else if (call_Method instanceof CtConstructor) {
				CtConstructor srcCon = (CtConstructor) call_Method;
				blk2 = srcCon.getBody();
			}

			// F1 metrics (context)
			// LOC of source mtd
			int LOC_Src = getLOC(blk);
			// LOC of extracted mtd
			LOC_Extracted_Method = getLOC(extracted_Code);
			int LOC_Call = getLOC(blk2);
			// LOC of context
			int Con_LOC = (LOC_Call - 1) > 0 ? (LOC_Call - 1) : 0;
			List<CtLocalVariable> con_local = blk2.getElements(new TypeFilter(CtLocalVariable.class));
			con_local = filterNull(con_local);
			int CON_LOCAL = con_local.size();

			List<CtLiteral> con_literal = blk2.getElements(new TypeFilter(CtLiteral.class));
			con_literal = filterNull(con_literal);
			con_literal = filterNum(con_literal);
			int CON_LITERAL = con_literal.size() > 0 ? 1 : 0;

			List<CtAssert> con_assert = blk2.getElements(new TypeFilter(CtAssert.class));
			con_assert = filterNull(con_assert);
			int CON_ASSERT = con_assert.size();

			List<CtInvocation> con_invo = blk2.getElements(new TypeFilter(CtInvocation.class));
			con_invo = filterNull(con_invo);
			int CON_INVOCATION = con_invo.size();

			List<CtIf> con_if = blk2.getElements(new TypeFilter(CtIf.class));
			con_if = filterNull(con_if);
			int CON_IF = con_if.size();

			List<CtConditional> con_conditional = blk2.getElements(new TypeFilter(CtConditional.class));
			con_conditional = filterNull(con_conditional);
			int CON_CONDITIONAL = con_conditional.size();

			List<CtSwitch> con_switch = blk2.getElements(new TypeFilter(CtSwitch.class));
			con_switch = filterNull(con_switch);
			int CON_SWITCH = con_switch.size();

			List<CtVariableAccess> con_var_access = blk2.getElements(new TypeFilter(CtVariableAccess.class));
			con_var_access = filterNull(con_var_access);
			int CON_VAR_ACC = con_var_access.size();

			List<CtTypeAccess> con_type_access = blk2.getElements(new TypeFilter(CtTypeAccess.class));
			con_type_access = filterNull(con_type_access);
			int CON_TYPE_ACC = con_type_access.size();

			List<CtFieldAccess> con_field_access = blk2.getElements(new TypeFilter(CtFieldAccess.class));
			con_field_access = filterNull(con_field_access);
			int CON_FIELD_ACC = con_field_access.size();

			List<CtAssignment> con_assign = blk2.getElements(new TypeFilter(CtAssignment.class));
			con_assign = filterNull(con_assign);
			int CON_ASSIGN = con_assign.size();

			List<CtTypedElement> con_typed_ele = blk2.getElements(new TypeFilter(CtTypedElement.class));
			con_typed_ele = filterNull(con_typed_ele);
			int CON_TYPED_ELE = con_typed_ele.size();

			List<CtPackageReferenceImpl> con_package = blk2.getElements(new TypeFilter(CtPackageReferenceImpl.class));
			con_package = filterNull(con_package);
			int CON_PACKAGE = con_package.size();

			double[] temp_result = new double[2];
			temp_result[0] = temp_result[1] = 0;
			double ratio_LOC = 0;
			// F2 metrics
			// variable
			Num_Variable = filterNull(deleted.getElements(new TypeFilter(CtVariable.class))).size();
			Num_local = filterNull(deleted.getElements(new TypeFilter(CtLocalVariable.class))).size();
			// Literal
			Num_Literal = filterNull(deleted.getElements(new TypeFilter(CtLiteral.class))).size() > 0 ? 1 : 0;
			// Invocation
			Num_Invocation = filterNull(deleted.getElements(new TypeFilter(CtInvocation.class))).size();
			// Structure
			Num_If = filterNull(deleted.getElements(new TypeFilter(CtIf.class))).size();
			Num_Conditional = filterNull(deleted.getElements(new TypeFilter(CtConditional.class))).size();
			Num_Switch = filterNull(deleted.getElements(new TypeFilter(CtSwitch.class))).size();
			// Access
			Num_Var_Ac = filterNull(deleted.getElements(new TypeFilter(CtVariableAccess.class))).size();
			Num_Type_Ac = filterNull(deleted.getElements(new TypeFilter(CtTypeAccess.class))).size();
			Num_Field_Ac = filterNull(deleted.getElements(new TypeFilter(CtFieldAccess.class))).size();
			Num_Assign = filterNull(deleted.getElements(new TypeFilter(CtAssignment.class))).size();

			// F3 the ratio of frequency of variable access in the deleted
			// part to that in src
			delVarAcc = new ArrayList<CtVariableAccess>(deleted.getElements(new TypeFilter(CtVariableAccess.class)));
			srcVarAcc = new ArrayList<CtVariableAccess>(blk.getElements(new TypeFilter(CtVariableAccess.class)));
			System.out.println("Variable Access that almost only used in the deleted part is: ");
			double Ratio_Variable_Access = ratio_u(temp_result, delVarAcc, srcVarAcc, variable_access_most_used);
			double Ratio_Variable_Access2 = temp_result[1];

			// F3 the ratio of frequency of field access in the deleted part
			// to that in src
			delFieldAcc = new ArrayList<CtFieldAccess>(deleted.getElements(new TypeFilter(CtFieldAccess.class)));
			srcFieldAcc = new ArrayList<CtFieldAccess>(blk.getElements(new TypeFilter(CtFieldAccess.class)));
			System.out.println("Field Access that almost only used in the deleted part is: ");
			double Ratio_Field_Access = ratio_u(temp_result, delFieldAcc, srcFieldAcc, field_access_most_used);
			double Ratio_Field_Access2 = temp_result[1];

			// F3 the ratio of frequency of invocation in the deleted part
			// to that in src
			if (LOC_Src > 0) {
				ratio_LOC = LOC_Extracted_Method / (double) LOC_Src;
			}

			delInvo = new ArrayList<CtInvocation>(deleted.getElements(new TypeFilter(CtInvocation.class)));
			srcInvo = new ArrayList<CtInvocation>(blk.getElements(new TypeFilter(CtInvocation.class)));
			System.out.println("Invocation that almost only used in the deleted part is: ");
			double Ratio_Invocation = ratio_u(temp_result, delInvo, srcInvo, invocation_most_used);
			double Ratio_Invocation2 = temp_result[1];

			// F3 the ratio of frequency of type access in the deleted part
			// to that in src
			delTypeAcc = new ArrayList<CtTypeAccess>(deleted.getElements(new TypeFilter(CtTypeAccess.class)));
			srcTypeAcc = new ArrayList<CtTypeAccess>(blk.getElements(new TypeFilter(CtTypeAccess.class)));
			System.out.println("Type Access that almost only used in the deleted part is: ");
			double Ratio_Type_Access = ratio_u(temp_result, delTypeAcc, srcTypeAcc, type_access_most_used);
			double Ratio_Type_Access2 = temp_result[1];

			// F3 the ratio of frequency of typed element in the deleted
			// part to that in src
			delTypedEle = new ArrayList<CtTypedElement>(deleted.getElements(new TypeFilter(CtTypedElement.class)));
			srcTypedEle = new ArrayList<CtTypedElement>(blk.getElements(new TypeFilter(CtTypedElement.class)));
			System.out.println("Typed element that almost only used in the deleted part is: ");
			int Num_Typed_Ele = delTypedEle.size();
			double Ratio_Typed_Ele = ratio_u(temp_result, delTypedEle, srcTypedEle, typed_ele_most_used);
			double Ratio_Typed_Ele2 = temp_result[1];

			// F3 the ratio of frequency of packages in the deleted part to
			// that in src
			List<CtPackageReferenceImpl> delPackage = new ArrayList<CtPackageReferenceImpl>(
					deleted.getElements(new TypeFilter(CtPackageReferenceImpl.class)));
			List<CtPackageReferenceImpl> srcPackage = new ArrayList<CtPackageReferenceImpl>(
					blk.getElements(new TypeFilter(CtPackageReferenceImpl.class)));
			int Num_Package = delPackage.size();
			System.out.println("Package that almost only used in the deleted part is: ");
			double Ratio_Package = ratio(temp_result, delPackage, srcPackage, package_most_used);
			double Ratio_Package2 = temp_result[1];

			// Cohesion of Package
			double Coh_Pacakge = 0;
			if (LOC_Extracted_Method > 0) {
				Coh_Pacakge = Ratio_Package / (double) LOC_Extracted_Method;
			}

			// Print
			if (Con_LOC > 0) {
				printer.printRecord(Name_Ext_Mtd, Con_LOC, CON_LOCAL, CON_LITERAL, CON_INVOCATION, CON_IF,
						CON_CONDITIONAL, CON_SWITCH, CON_VAR_ACC, CON_TYPE_ACC, CON_FIELD_ACC, CON_ASSERT, CON_ASSIGN,
						CON_TYPED_ELE, CON_PACKAGE, LOC_Extracted_Method, Num_Variable, Num_local, Num_Literal,
						Num_Invocation, Num_If, Num_Conditional, Num_Switch, Num_Var_Ac, Num_Type_Ac, Num_Field_Ac,
						Num_Assign, Num_Typed_Ele, Num_Package, ratio_LOC, Ratio_Variable_Access,
						Ratio_Variable_Access2, Ratio_Field_Access, Ratio_Field_Access2, Ratio_Type_Access,
						Ratio_Type_Access2, Ratio_Typed_Ele, Ratio_Typed_Ele2, Ratio_Package, Ratio_Package2,
						Coh_Pacakge);
				printer.flush();
			} else {
				System.out.println("extract the whole thing!");
			}
			printer.close();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	private int getLOC(CtBlock cblk) {
		// TODO get lines of code
		int lines = 0;
		String blk = cblk.toString();
		char[] ch = blk.toCharArray();
		for (int i = 0; i < ch.length; i++) {
			if (ch[i] == '\n') {
				lines++;
			}
		}
		return lines;
	}

	private double ratio(double[] ratio, List<CtPackageReferenceImpl> delPackage,
			List<CtPackageReferenceImpl> srcPackage, CtPackageReferenceImpl pkg) {
		// TODO Auto-generated method stub
		List<CtPackageReferenceImpl> parPackage = new ArrayList<CtPackageReferenceImpl>();
		List<CtParameter> params = new ArrayList<CtParameter>();
		if (extracted_Method instanceof CtMethod) {
			params = ((CtMethod) extracted_Method).getParameters();
		} else if (extracted_Method instanceof CtConstructor) {
			params = ((CtConstructor) extracted_Method).getParameters();
		}
		for (int p = 0; p < params.size(); p++) {
			CtParameter par = params.get(p);
			List<CtPackageReferenceImpl> ttt = par.getType().getElements(new TypeFilter(CtPackageReferenceImpl.class));
			for (int k = 0; k < ttt.size(); k++) {
				parPackage.add(ttt.get(k));
			}
		}
		List<CtPackageReferenceImpl> delPackage2 = getNewList(delPackage);
		for (int l = 0; l < delPackage2.size(); l++) {
			CtPackageReferenceImpl tem = delPackage2.get(l);
			if (parPackage.contains(tem)) {
				delPackage2.remove(delPackage2.indexOf(tem));
				l--;
			}
		}
		int num1, num2;
		CtPackageReferenceImpl temp;
		int size = delPackage2.size();
		double[] all_ratios = new double[size];
		for (int i = 0; i < size; i++) {
			temp = delPackage2.get(i);
			num1 = Collections.frequency(delPackage, temp);
			num2 = Collections.frequency(srcPackage, temp);
			if (num2 != 0) {
				all_ratios[i] = num1 / (double) num2;
			} else {
				all_ratios[i] = 0;
			}
		}
		double result = 0;
		double result2 = 0;
		int index = -1;
		for (int j = 0; j < size; j++) {
			if (all_ratios[j] > result) {
				index = j;
				result2 = result;
				result = all_ratios[j];
			}
		}
		if (index == -1) {
			System.out.println("No package used in the code");
		} else {
			System.out.println("the most used package: " + delPackage2.get(index));
			pkg = delPackage2.get(index);
		}
		if (result > 1) {
			result = 1;
		}
		ratio[0] = result;
		ratio[1] = result2;
		return result;
	}

	private <T> double ratio_u(double[] ratio, List<T> delPackage, List<T> srcPackage, T pkg) {
		// TODO Auto-generated method stub
		List<T> delPackage2 = getNewList(delPackage);
		int num1, num2;
		T temp;
		int size = delPackage2.size();
		double[] all_ratios = new double[size];
		for (int i = 0; i < size; i++) {
			temp = delPackage2.get(i);
			num1 = Collections.frequency(delPackage, temp);
			num2 = Collections.frequency(srcPackage, temp);
			if (num2 != 0) {
				all_ratios[i] = num1 / (double) num2;
			} else {
				all_ratios[i] = 0;
			}
		}
		double result = 0;
		double result2 = 0;
		int index = -1;
		for (int j = 0; j < size; j++) {
			if (all_ratios[j] > result) {
				index = j;
				result2 = result;
				result = all_ratios[j];
			}
		}
		if (index == -1) {
			System.out.println("Nothing used in the code");
		} else {
			System.out.println("the most used element: " + delPackage2.get(index));
			pkg = delPackage2.get(index);
		}
		if (result > 1) {
			result = 1;
		}
		ratio[0] = result;
		ratio[1] = result2;
		return result;
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
			if (!((element.getClass().getSimpleName().substring(2, element.getClass().getSimpleName().length() - 4))
					.equalsIgnoreCase("Try"))) {
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
				System.out.println(element.toString());
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
							// callMethod.add(te2);
						} else if (te2.getSimpleName().toString().equals(Name_Ext_Mtd) && flagtemp == false) {
							flagtemp = true;
							System.out.println("--------------------A new method is inserted!");
							// extracted_Method = te2;
						}
					} else if (element.toString().contains(Name_Ext_Mtd) && !nodeType.equalsIgnoreCase("Constructor")) {
						CtElement callIt = element;
						while (!(callIt instanceof CtMethod) && !(callIt instanceof CtConstructor)
								&& !(callIt instanceof CtClass)) {
							callIt = callIt.getParent();
							System.out.println("========" + callIt);
						}
						if (callIt instanceof CtMethod) {
							System.out.println("+++++++++++");
							CtMethod m = (CtMethod) callIt;
							if (m.getSimpleName().toString().equals(Name_Src_Mtd)) {
								// callMethod.add((CtMethod) callIt);
							}
						} else if (callIt instanceof CtConstructor) {
							CtConstructor m = (CtConstructor) callIt;
							while (!(callIt instanceof CtClass)) {
								callIt = callIt.getParent();
							}
							CtClass class_name = (CtClass) callIt;
							System.out.println("class name:" + class_name.getSimpleName());
							if (class_name.getSimpleName().equals(Name_Src_Mtd)) {
								System.out.println("extract from constructor!");
								// callMethod.add(m);
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
								// sourceMethod.add(src_temp);
							}
						} else if (callIt instanceof CtConstructor) {
							CtConstructor m = (CtConstructor) callIt;
							while (!(callIt instanceof CtClass)) {
								callIt = callIt.getParent();
							}
							CtClass class_name = (CtClass) callIt;
							System.out.println("class name:" + class_name.getSimpleName());
							if (class_name.getSimpleName().equals(Name_Src_Mtd)) {
								System.out.println("extract from constructor!");
								deleteStuff.add(element);
								// sourceMethod.add(m);
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
									// sourceMethod.add(temp_method);
								}
							} else if (callIt instanceof CtConstructor) {
								CtConstructor m = (CtConstructor) callIt;
								while (!(callIt instanceof CtClass)) {
									callIt = callIt.getParent();
								}
								CtClass class_name = (CtClass) callIt;
								System.out.println("class name:" + class_name.getSimpleName());
								if (class_name.getSimpleName().equals(Name_Src_Mtd)) {
									System.out.println("extract from constructor!");
									deleteStuff.add(element);
									// sourceMethod.add(m);
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

				String label = null;
				if (!element.equals(null)) {
					label = element.toString();
				}
				if (action instanceof Update) {
					CtElement callIt = element;
					while (!(callIt instanceof CtMethod) && !(callIt instanceof CtConstructor)
							&& !(callIt instanceof CtClass)) {
						callIt = callIt.getParent();
					}
					if (callIt instanceof CtMethod) {
						CtMethod temp_method = (CtMethod) callIt;
						if (temp_method.getSimpleName().toString().equals(Name_Src_Mtd)) {
							// sourceMethod.add(temp_method);
						}
					} else if (callIt instanceof CtConstructor) {
						CtConstructor m = (CtConstructor) callIt;
						while (!(callIt instanceof CtClass)) {
							callIt = callIt.getParent();
						}
						CtClass class_name = (CtClass) callIt;
						System.out.println("class name:" + class_name.getSimpleName());
						if (class_name.getSimpleName().equals(Name_Src_Mtd)) {
							System.out.println("extract from constructor!");
							deleteStuff.add(element);
							// sourceMethod.add(m);
						}
					}
					CtElement elementDest = (CtElement) action.getNode()
							.getMetadata(SpoonGumTreeBuilder.SPOON_OBJECT_DEST);
					if (elementDest instanceof CtMethod) {
						CtMethod temp_dest = (CtMethod) elementDest;
						if (flagtemp == false && temp_dest.getSimpleName().toString().equals(Name_Ext_Mtd)) {
							flagtemp = true;
							// extracted_Method = temp_dest;
							System.out.println("--------------------A new method is updated !");
						} else if (temp_dest.getSimpleName().equals(Name_Src_Mtd)
								&& temp_dest.toString().contains(Name_Ext_Mtd)) {
							// callMethod.add(temp_dest);
						}
					} else if (!nodeType.equalsIgnoreCase("Constructor")
							&& elementDest.toString().contains(Name_Ext_Mtd)) {
						CtElement callIt1 = elementDest;
						while (!(callIt1 instanceof CtMethod) && !(callIt1 instanceof CtConstructor)
								&& !(callIt1 instanceof CtClass)) {
							callIt1 = callIt1.getParent();
						}
						if (callIt1 instanceof CtMethod) {
							// callMethod.add((CtMethod) callIt1);
						} else if (callIt instanceof CtConstructor) {
							CtConstructor m = (CtConstructor) callIt;
							while (!(callIt instanceof CtClass)) {
								callIt = callIt.getParent();
							}
							CtClass class_name = (CtClass) callIt;
							System.out.println("class name:" + class_name.getSimpleName());
							if (class_name.getSimpleName().equals(Name_Src_Mtd)) {
								System.out.println("extract from constructor!");
								// callMethod.add(m);
							}
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
