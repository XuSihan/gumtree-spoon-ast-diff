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
import java.util.Random;
import java.util.stream.Collectors;

import org.apache.commons.csv.CSVFormat;
import org.apache.commons.csv.CSVPrinter;

// import org.apache.log4j.Level;
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
import spoon.reflect.code.CtCodeSnippetStatement;
import spoon.reflect.code.CtComment;
import spoon.reflect.code.CtConditional;
import spoon.reflect.code.CtExecutableReferenceExpression;
import spoon.reflect.code.CtFieldAccess;
import spoon.reflect.code.CtIf;
import spoon.reflect.code.CtInvocation;
import spoon.reflect.code.CtLiteral;
import spoon.reflect.code.CtLocalVariable;
import spoon.reflect.code.CtStatement;
import spoon.reflect.code.CtSwitch;
import spoon.reflect.code.CtTypeAccess;
import spoon.reflect.code.CtVariableAccess;
import spoon.reflect.declaration.CtClass;
import spoon.reflect.declaration.CtConstructor;
import spoon.reflect.declaration.CtElement;
import spoon.reflect.declaration.CtExecutable;
import spoon.reflect.declaration.CtMethod;
import spoon.reflect.declaration.CtModifiable;
import spoon.reflect.declaration.CtPackage;
import spoon.reflect.declaration.CtParameter;
import spoon.reflect.declaration.CtType;
import spoon.reflect.declaration.CtTypedElement;
import spoon.reflect.declaration.CtVariable;
import spoon.reflect.factory.Factory;
// import spoon.reflect.factory.Factory;
import spoon.reflect.factory.FactoryImpl;
import spoon.reflect.visitor.filter.TypeFilter;
import spoon.support.DefaultCoreFactory;
import spoon.support.StandardEnvironment;
import spoon.support.reflect.reference.CtPackageReferenceImpl;
// import spoon.reflect.factory.CodeFactory;;;

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

	List<CtElement> callMethod = new ArrayList<CtElement>(); // after
																// version里的source
																// method
	List<CtElement> sourceMethod = new ArrayList<CtElement>(); // before
																// version里的source
																// method
	List<CtElement> deleteStuff = new ArrayList<CtElement>(); // before
																// version里source
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

	public DiffImpl(TreeContext context, ITree rootSpoonLeft, ITree rootSpoonRight, String Extracted_Mtd,
			String Src_Mtd) {
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
		List<T> list = new ArrayList<T>();
		for (int i = 0; i < li.size(); i++) {
			T str = li.get(i); // 获取传入集合对象的每一个元素
			if (!list.contains(str)) { // 查看新集合中是否有指定的元素，如果没有则加入
				list.add(str);
			}
		}
		return list; // 返回集合
	}

	public static <T> List<T> minusList(List<T> src, List<T> deleted) {
		List<T> list = new ArrayList<T>(src);
		List<T> list2 = new ArrayList<T>(deleted);
		System.out.println("copy src: " + list.toString());
		System.out.println("copy deleted: " + list2.toString());
		for (int i = 0; i < list2.size(); i++) {
			T str = list2.get(i); // 获取传入集合对象的每一个元素
			if (list.contains(str)) { // 查看新集合中是否有指定的元素，如果没有则加入
				list.remove(str);
				list2.remove(str);
				i--;
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
				+ "-------------------Methods who call it--------------------" + callMethod.size() + "\n" + "\n");
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
			System.out.println("the code is: " + tempEl.toString() + "the similarity of this stuff is: " + sim2);
			if (sim2 > sim1) {
				deleted = tempEl;
				sim1 = sim2;
			}
		}
		if (size3 == 0 || sim(deleted.toString(), extracted_Method.getBody().toString()) < 0.6) {
			deleted = extracted_Method.getBody();
			System.out.println("use extracted method directly");
		}
		File file_before = new File("before_method");
		file_before.createNewFile();
		FileWriter fileWriter2 = new FileWriter(file_before);
		fileWriter2.write("-----------------------Extracted Part---------------------" + "\n" + "\n"
				+ deleted.toString() + "\n" + "\n");
		fileWriter2.write("--------------------------Source Methods------------------------------" + "\n" + "\n");
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
		File file = new File("con_neg.csv");
		CSVFormat format = null;
		if (file.exists()) {
			format = CSVFormat.DEFAULT.withHeader("Src_LOC", "Src_Num_local", "Src_Num_Literal", "Src_Num_Invocation",
					"Src_Num_If", "Src_Num_Conditional", "Src_Num_Switch", "Src_Num_Var_Ac", "Src_Num_Type_Ac",
					"Src_Num_Field_Ac", "Src_Num_Assert", "Src_Num_Assign", "Src_Num_Typed_Ele", "Src_Num_Package",
					"LOC_Extracted_Method", "Num_Variable", "Num_local", "Num_Literal", "Num_Invocation", "Num_If",
					"Num_Conditional", "Num_Switch", "Num_Var_Ac", "Num_Type_Ac", "Num_Field_Ac", "Num_Assign",
					"Num_Typed_Ele", "Num_Package", "ratio_LOC", "Ratio_Variable_Access", "Ratio_Field_Access",
					"Ratio_Type_Access", "Ratio_Typed_Ele", "Ratio_Package").withSkipHeaderRecord();
		} else {
			format = CSVFormat.DEFAULT.withHeader("Src_LOC", "Src_Num_local", "Src_Num_Literal", "Src_Num_Invocation",
					"Src_Num_If", "Src_Num_Conditional", "Src_Num_Switch", "Src_Num_Var_Ac", "Src_Num_Type_Ac",
					"Src_Num_Field_Ac", "Src_Num_Assert", "Src_Num_Assign", "Src_Num_Typed_Ele", "Src_Num_Package",
					"LOC_Extracted_Method", "Num_Variable", "Num_local", "Num_Literal", "Num_Invocation", "Num_If",
					"Num_Conditional", "Num_Switch", "Num_Var_Ac", "Num_Type_Ac", "Num_Field_Ac", "Num_Assign",
					"Num_Typed_Ele", "Num_Package", "ratio_LOC", "Ratio_Variable_Access", "Ratio_Field_Access",
					"Ratio_Type_Access", "Ratio_Typed_Ele", "Ratio_Package");
		}
		try (Writer out = new FileWriter("con_neg.csv", true); CSVPrinter printer = new CSVPrinter(out, format)) {
			System.out.println("--------------source method----------------" + sourceMethod.size());
			for (int w = 0; w < sourceMethod.size(); w++) {

				// get the body of source method: blk
				CtBlock blk = null;
				if (sourceMethod.get(w) instanceof CtMethod) {
					CtMethod m = (CtMethod) sourceMethod.get(w);
					blk = m.getBody();
				} else if (sourceMethod.get(w) instanceof CtConstructor) {
					CtConstructor constr = (CtConstructor) sourceMethod.get(w);
					blk = constr.getBody();
				}

				// 生成负例
				// 初始化一个空cblk
				// System.out.println("should be empty:" + cblk.toString());

				// 根据source method(blk)随机生成statement lists作为cblk
				// cblk = getRandomStat(blk);
				List<CtBlock> exhau_candi = getAllCandi(blk);
				System.out.println("-=-=-=-=-=: " + exhau_candi);
				File candidates = new File("candidates");
				candidates.createNewFile();
				FileWriter fileWriter2 = new FileWriter(candidates);
				for (int kl = 0; kl < exhau_candi.size(); kl++) {
					deleted = exhau_candi.get(kl);
					CtBlock cblk = exhau_candi.get(kl);

					fileWriter2.write("-----------------------candidate" + kl + "---------------------" + "\n" + "\n"
							+ deleted.toString() + "\n" + "\n");
					int start = cblk.getStatement(0).getPosition().getLine();
					int end = cblk.getLastStatement().getPosition().getLine();
					fileWriter2.write("start: " + start);
					fileWriter2.write("end: " + end);
					// get the context
					// F1 metrics (context)
					LOC_Extracted_Method = cblk.getStatements().size();
					int Src_LOC = getContex(blk, cblk);
					int Src_Num_local = minusList(blk.getElements(new TypeFilter(CtLocalVariable.class)),
							deleted.getElements(new TypeFilter(CtLocalVariable.class))).size();
					int Src_Num_Literal = minusList(blk.getElements(new TypeFilter(CtLiteral.class)),
							deleted.getElements(new TypeFilter(CtLiteral.class))).size();
					int Src_Num_Assert = minusList(blk.getElements(new TypeFilter(CtAssert.class)),
							deleted.getElements(new TypeFilter(CtAssert.class))).size();
					int Src_Num_Com = minusList(blk.getElements(new TypeFilter(CtComment.class)),
							deleted.getElements(new TypeFilter(CtComment.class))).size();
					int Src_Num_Invocation = minusList(blk.getElements(new TypeFilter(CtInvocation.class)),
							deleted.getElements(new TypeFilter(CtInvocation.class))).size();
					int Src_Num_Executable = minusList(blk.getElements(new TypeFilter(CtExecutable.class)),
							deleted.getElements(new TypeFilter(CtExecutable.class))).size();
					int Src_Num_ExeRefExp = minusList(
							blk.getElements(new TypeFilter(CtExecutableReferenceExpression.class)),
							deleted.getElements(new TypeFilter(CtExecutableReferenceExpression.class))).size();
					int Src_Num_If = minusList(blk.getElements(new TypeFilter(CtIf.class)),
							deleted.getElements(new TypeFilter(CtIf.class))).size();
					int Src_Num_Conditional = minusList(blk.getElements(new TypeFilter(CtConditional.class)),
							deleted.getElements(new TypeFilter(CtConditional.class))).size();
					int Src_Num_Switch = minusList(blk.getElements(new TypeFilter(CtSwitch.class)),
							deleted.getElements(new TypeFilter(CtSwitch.class))).size();
					int Src_Num_Var_Ac = minusList(blk.getElements(new TypeFilter(CtVariableAccess.class)),
							deleted.getElements(new TypeFilter(CtVariableAccess.class))).size();
					int Src_Num_Type_Ac = minusList(blk.getElements(new TypeFilter(CtTypeAccess.class)),
							deleted.getElements(new TypeFilter(CtTypeAccess.class))).size();
					int Src_Num_Field_Ac = minusList(blk.getElements(new TypeFilter(CtFieldAccess.class)),
							deleted.getElements(new TypeFilter(CtFieldAccess.class))).size();
					int Src_Num_Assign = minusList(blk.getElements(new TypeFilter(CtAssignment.class)),
							deleted.getElements(new TypeFilter(CtAssignment.class))).size();
					int Src_Num_Typed_Ele = minusList(blk.getElements(new TypeFilter(CtTypedElement.class)),
							deleted.getElements(new TypeFilter(CtTypedElement.class))).size();
					int Src_Num_Package = minusList(blk.getElements(new TypeFilter(CtPackageReferenceImpl.class)),
							deleted.getElements(new TypeFilter(CtPackageReferenceImpl.class))).size();
					double ratio_LOC = 0;
					// F2 metrics
					if (blk.getStatements().size() > 0) {
						ratio_LOC = LOC_Extracted_Method / (double) blk.getStatements().size();
					}
					// variable
					Num_Variable = deleted.getElements(new TypeFilter(CtVariable.class)).size();
					Num_local = deleted.getElements(new TypeFilter(CtLocalVariable.class)).size();
					// Literal
					Num_Literal = deleted.getElements(new TypeFilter(CtLiteral.class)).size();
					// Invocation
					Num_Invocation = deleted.getElements(new TypeFilter(CtInvocation.class)).size();
					// Structure
					Num_If = deleted.getElements(new TypeFilter(CtIf.class)).size();
					Num_Conditional = deleted.getElements(new TypeFilter(CtConditional.class)).size();
					Num_Switch = deleted.getElements(new TypeFilter(CtSwitch.class)).size();
					// Access
					Num_Var_Ac = deleted.getElements(new TypeFilter(CtVariableAccess.class)).size();
					Num_Type_Ac = deleted.getElements(new TypeFilter(CtTypeAccess.class)).size();
					Num_Field_Ac = deleted.getElements(new TypeFilter(CtFieldAccess.class)).size();
					Num_Assign = deleted.getElements(new TypeFilter(CtAssignment.class)).size();

					// F3 the ratio of frequency of variable access in the deleted
					// part to that in src
					delVarAcc = new ArrayList<CtVariableAccess>(
							deleted.getElements(new TypeFilter(CtVariableAccess.class)));
					srcVarAcc = new ArrayList<CtVariableAccess>(
							blk.getElements(new TypeFilter(CtVariableAccess.class)));
					System.out.println("Variable Access that almost only used in the deleted part is: ");
					double Ratio_Variable_Access = ratio_u(delVarAcc, srcVarAcc, variable_access_most_used);

					// F3 the ratio of frequency of field access in the deleted part
					// to that in src
					delFieldAcc = new ArrayList<CtFieldAccess>(
							deleted.getElements(new TypeFilter(CtFieldAccess.class)));
					srcFieldAcc = new ArrayList<CtFieldAccess>(blk.getElements(new TypeFilter(CtFieldAccess.class)));
					System.out.println("Field Access that almost only used in the deleted part is: ");
					double Ratio_Field_Access = ratio_u(delFieldAcc, srcFieldAcc, field_access_most_used);

					// F3 the ratio of frequency of invocation in the deleted part
					// to that in src
					delInvo = new ArrayList<CtInvocation>(deleted.getElements(new TypeFilter(CtInvocation.class)));
					srcInvo = new ArrayList<CtInvocation>(blk.getElements(new TypeFilter(CtInvocation.class)));
					System.out.println("Invocation that almost only used in the deleted part is: ");
					double Ratio_Invocation = ratio_u(delInvo, srcInvo, invocation_most_used);

					// F3 the ratio of frequency of type access in the deleted part
					// to that in src
					delTypeAcc = new ArrayList<CtTypeAccess>(deleted.getElements(new TypeFilter(CtTypeAccess.class)));
					srcTypeAcc = new ArrayList<CtTypeAccess>(blk.getElements(new TypeFilter(CtTypeAccess.class)));
					System.out.println("Type Access that almost only used in the deleted part is: ");
					double Ratio_Type_Access = ratio_u(delTypeAcc, srcTypeAcc, type_access_most_used);

					// F3 the ratio of frequency of typed element in the deleted
					// part to that in src
					delTypedEle = new ArrayList<CtTypedElement>(
							deleted.getElements(new TypeFilter(CtTypedElement.class)));
					srcTypedEle = new ArrayList<CtTypedElement>(blk.getElements(new TypeFilter(CtTypedElement.class)));
					System.out.println("Typed element that almost only used in the deleted part is: ");
					int Num_Typed_Ele = delTypedEle.size();
					double Ratio_Typed_Ele = ratio_u(delTypedEle, srcTypedEle, typed_ele_most_used);

					// F3 the ratio of frequency of packages in the deleted part to
					// that in src
					List<CtPackageReferenceImpl> delPackage = new ArrayList<CtPackageReferenceImpl>(
							deleted.getElements(new TypeFilter(CtPackageReferenceImpl.class)));
					List<CtPackageReferenceImpl> srcPackage = new ArrayList<CtPackageReferenceImpl>(
							blk.getElements(new TypeFilter(CtPackageReferenceImpl.class)));
					int Num_Package = delPackage.size();
					System.out.println("Package that almost only used in the deleted part is: ");
					double Ratio_Package = ratio(delPackage, srcPackage, package_most_used);
					// Print
					if (Src_LOC >= 0) {
						printer.printRecord(Src_LOC, Src_Num_local, Src_Num_Literal, Src_Num_Invocation, Src_Num_If,
								Src_Num_Conditional, Src_Num_Switch, Src_Num_Var_Ac, Src_Num_Type_Ac, Src_Num_Field_Ac,
								Src_Num_Assert, Src_Num_Assign, Src_Num_Typed_Ele, Src_Num_Package,
								LOC_Extracted_Method, Num_Variable, Num_local, Num_Literal, Num_Invocation, Num_If,
								Num_Conditional, Num_Switch, Num_Var_Ac, Num_Type_Ac, Num_Field_Ac, Num_Assign,
								Num_Typed_Ele, Num_Package, ratio_LOC, Ratio_Variable_Access, Ratio_Field_Access,
								Ratio_Type_Access, Ratio_Typed_Ele, Ratio_Package);
						printer.flush();
					}
				}
				fileWriter2.close();
			}
			printer.close();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	private int getContex(CtBlock blk, CtBlock cblk) {
		// 获取context的loc
		int n = 0;
		// CtBlock con = newBlock(cblk);
		int min_pos = cblk.getStatement(0).getPosition().getLine();
		int max_pos = cblk.getLastStatement().getPosition().getLine();
		System.out.println("start position: " + min_pos);
		System.out.println("end position: " + max_pos);
		CtStatement temp;
		for (int i = 0; i < blk.getStatements().size(); i++) {
			temp = blk.getStatement(i);
			if (blk.getStatement(i).getPosition().getLine() < min_pos) {
				// con.addStatement(temp);
				if ((i + 1) < blk.getStatements().size()) {
					if (blk.getStatement(i + 1).getPosition().getLine() <= min_pos) {
						n++;
					}
				}
			} else if (blk.getStatement(i).getPosition().getLine() > max_pos) {
				// con.addStatement(temp);
				n++;
			}
		}
		return n;
	}

	private CtBlock getRandomStat(CtBlock blk) {
		// 随机选一个block，并随机选择其中的几个相邻的语句
		// 生成一个空的cblk
		CtBlock cblk = newBlock(blk);

		// 获取全部的blocks
		List<CtBlock> all_blocks = blk.getElements(new TypeFilter(CtBlock.class));
		System.out.println("number of blocks: " + all_blocks.size());

		// 随机获取一个block
		int random = genRandom(0, all_blocks.size() - 1);
		CtBlock tblk = all_blocks.get(random);

		// 随机获取相邻的语句
		int size = tblk.getStatements().size();
		int start = genRandom(0, size - 1);
		int end = genRandom(start, size - 1);
		for (int i = start; i <= end; i++) {
			cblk.addStatement(tblk.getStatement(i));
		}
		if (start == end && (cblk.toString().contains("break;") || cblk.toString().contains("return")
				|| cblk.toString().contains("continue;"))) {
			getRandomStat(blk);
		}
		System.out.println("should not be empty: " + cblk.toString());
		return cblk;
	}

	private List<CtBlock> getAllCandi(CtBlock blk) {
		// 随机选一个block，并随机选择其中的几个相邻的语句
		// 生成一个空的block lists
		List<CtBlock> candidates = new ArrayList<CtBlock>();

		// 获取全部的blocks
		List<CtBlock> all_blocks = blk.getElements(new TypeFilter(CtBlock.class));
		System.out.println("number of blocks: " + all_blocks.size());
		for (int j = 0; j < all_blocks.size(); j++) {
			CtBlock temp = all_blocks.get(j);
			int blk_size = temp.getStatements().size();
			for (int z = 0; z < blk_size; z++) {
				for (int y = z; y < blk_size; y++) {
					CtBlock cblk = newBlock(blk);
					for (int q = z; q <= y; q++) {
						cblk.addStatement(temp.getStatement(q));
					}
					candidates.add(cblk);
				}
			}
		}
		return candidates;
	}

	private CtBlock newBlock(CtBlock blk) {
		// TODO Auto-generated method stub
		CtBlock cblk = blk.clone();
		for (int y = 0; y < cblk.getStatements().size(); y++) {
			cblk.removeStatement(cblk.getStatement(y));
			y--;
		}
		return cblk;
	}

	private boolean isToken(String string) {
		// 判断随机取出的子句是不是一个token语句
		boolean istoken = false;
		if (string.equals("break") || string.equals("return") || string.equals("continue")
				|| string.equals("default")) {
			istoken = true;
		}
		return istoken;
	}

	private CtBlock createBlock(String string) {
		// TODO Auto-generated method stub
		Factory factory = new FactoryImpl(new DefaultCoreFactory(), new StandardEnvironment());
		CtCodeSnippetStatement statementInConstructor = factory.Code().createCodeSnippetStatement(string);
		CtBlock CtBlockOfConstructor = factory.Code().createCtBlock(statementInConstructor);
		return CtBlockOfConstructor;
	}

	private int genRandom(int MIN, int MAX) {
		// 生成一个随机整数
		Random rand = new Random();
		return (rand.nextInt(MAX - MIN + 1) + MIN);
	}

	private double ratio(List<CtPackageReferenceImpl> delPackage, List<CtPackageReferenceImpl> srcPackage,
			CtPackageReferenceImpl pkg) {
		// 计算cohesion
		List<CtPackageReferenceImpl> parPackage = new ArrayList<CtPackageReferenceImpl>();
		for (int p = 0; p < extracted_Method.getParameters().size(); p++) {
			CtParameter par = (CtParameter) extracted_Method.getParameters().get(p);
			List<CtPackageReferenceImpl> ttt = par.getType().getElements(new TypeFilter(CtPackageReferenceImpl.class));
			for (int k = 0; k < ttt.size(); k++) {
				parPackage.add(ttt.get(k));
			}
		}
		List<CtPackageReferenceImpl> delPackage2 = getNewList(delPackage);
		for (int l = 0; l < delPackage2.size(); l++) {
			CtPackageReferenceImpl tem = delPackage2.get(l);
			if (parPackage.contains(tem)) {
				delPackage2.remove(tem);
				l--;
			}
		}
		System.out.println("------CtDelPackageReferenceImpl---------++" + delPackage2);
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
		int index = -1;
		for (int j = 0; j < size; j++) {
			if (all_ratios[j] > result) {
				index = j;
				result = all_ratios[j];
			}
		}
		if (index == -1) {
			System.out.println("No package used in the code");
		} else {
			System.out.println(" " + delPackage2.get(index));
			pkg = delPackage2.get(index);
		}
		if (result > 1) {
			result = 1;
		}
		return result;
	}

	private <T> double ratio_u(List<T> delPackage, List<T> srcPackage, T pkg) {
		// TODO Auto-generated method stub
		List<T> delPackage2 = getNewList(delPackage);
		System.out.println("------CtDel***Impl---------++" + delPackage2);
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
		int index = -1;
		for (int j = 0; j < size; j++) {
			if (all_ratios[j] > result) {
				index = j;
				result = all_ratios[j];
			}
		}
		if (index == -1) {
			System.out.println("Nothing used in the code");
		} else {
			System.out.println(" " + delPackage2.get(index));
			pkg = delPackage2.get(index);
		}
		if (result > 1) {
			result = 1;
		}
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
								callMethod.add((CtMethod) callIt);
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
								callMethod.add(m);
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
								sourceMethod.add(m);
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
									sourceMethod.add(m);
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
							sourceMethod.add(m);
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
						} else if (callIt instanceof CtConstructor) {
							CtConstructor m = (CtConstructor) callIt;
							while (!(callIt instanceof CtClass)) {
								callIt = callIt.getParent();
							}
							CtClass class_name = (CtClass) callIt;
							System.out.println("class name:" + class_name.getSimpleName());
							if (class_name.getSimpleName().equals(Name_Src_Mtd)) {
								System.out.println("extract from constructor!");
								callMethod.add(m);
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
