import z3
import os
current_dir = os.path.dirname(__file__)

# z3 basic definitions
ClassSort = z3.DeclareSort("ClassSort")
is_better_than = z3.Function("is_better_than", ClassSort, ClassSort, z3.BitVecSort(1))
x,y,z = z3.Consts('x y z', ClassSort)
transitivity = z3.ForAll([x,y,z], z3.Implies(z3.And(is_better_than(x,y)==1, is_better_than(y,z)==1), is_better_than(x,z)==1))
asymmetry = z3.ForAll([x,y], z3.Implies(is_better_than(x,y)==1, is_better_than(y,x)==0)) # asym (derives reflexivity)
completeness = z3.ForAll([x,y,z], z3.Implies(is_better_than(y,z)==1,
                                                z3.Or(is_better_than(x,y)==1,
                                                    is_better_than(y,x)==1,
                                                    is_better_than(x,z)==1,
                                                    is_better_than(z,x)==1,)))

def get_dsv_text_and_type(file_name):
    """
    Returns: a text.
    """
    try:
        f = open(file_name, "r")
    except:
        raise ValueError(f"no file {file_name} exists. Have you made the csv yet?")
    file_text = str(f.read())
    f.close()
    file_type = file_name[-3:]
    return file_text, file_type

def process_data(file_name, only_positive_judgements=False):
    data = get_dsv_text_and_type(file_name)[0]
    data_as_list = data.split('\n')
    processed_data = []
    for row in data_as_list:
        row_as_list = row.split(',')
        assert len(row_as_list) == 3, row_as_list
        if not only_positive_judgements:
            processed_data.append(row_as_list)
        elif row_as_list[2] != '':
            processed_data.append(row_as_list)
    return processed_data

errmsg = lambda x, y, z: f"the provided preference {z} is not one of the options in comparison ({x}, {y})"

def make_relations_set(processed_data):
    relations_set = set()
    for comparison in processed_data: # comparison is a list of 3 strings (representing classes)
        op1, op2, better_op = comparison
        assert better_op in (op1, op2) or better_op == '-', errmsg(op1, op2, better_op)
        worse_op = op1 if better_op == op2 else op2
        relations_set.add((better_op, worse_op))
    return relations_set

def solve(solver, constraints):
    result = solver.check(constraints)
    if result == z3.sat:
        return True, solver.model()
    return False, solver.unsat_core()

def solve_consistency(file_name, add_incompleteness=False, add_completeness=False):
    processed_data = process_data(file_name, only_positive_judgements=True)
    if len(processed_data) == 0:
        return f"no data in the file {file_name} so far"
    relations_set = make_relations_set(processed_data)
    constraints = []
    for relation in relations_set:
        class1_str, class2_str = relation
        cs1, cs2 = z3.Const(class1_str, ClassSort), z3.Const(class2_str, ClassSort)
        constraints.append(is_better_than(cs1, cs2)==1)
    constraints.append(transitivity)
    constraints.append(asymmetry)
    if add_incompleteness:
        constraints.append(z3.Not(completeness))
    if add_completeness:
        constraints.append(completeness)
    bsolver = z3.Solver()
    return solve(bsolver, constraints)
    
# def solve_incompleteness(processed_data)

def assign_values(bmodel):
    ClassSort = bmodel.get_sort(0)
    value = z3.Function("value", ClassSort, z3.IntSort())
    constraints = []
    Classes_list = []
    for i in range(len(bmodel)):
        if str(bmodel[i]) == 'is_better_than':
            is_better_than = bmodel[i]
        if isinstance(bmodel[bmodel[i]], z3.ExprRef):
            source_str_name = str(bmodel[i])
            Classes_list.append(z3.Const(source_str_name, ClassSort))
    for Class1 in Classes_list:
        constraints.append(value(Class1) > 0) # lower bound for readability
        for Class2 in Classes_list:
            if bmodel.evaluate(is_better_than(Class1,Class2)) == 1:
                constraints.append(value(Class1) > value(Class2)) # NOTE: THIS INVERTS DIRECTION OF RANKING
    vsolver = z3.Solver()
    return solve(vsolver, constraints)

def find_topological_order(file_name):
    bsat, bmodel = solve_consistency(file_name)
    if bsat:
        vsat, vmodel = assign_values(bmodel)
    else:
        unsat_core = bmodel
        return unsat_core
    if vsat:
        ClassSort = vmodel.get_sort(0)
        for i in range(len(vmodel)):
            if str(vmodel[i]) == 'value':
                value = lambda x: int(vmodel.evaluate(vmodel[i](x)).as_string())
                break
        td = {}
        for j in range(len(vmodel)):
            if isinstance(vmodel[vmodel[j]], z3.ExprRef):
                Class = z3.Const(str(vmodel[j]), ClassSort)
                if value(Class) not in td:
                    td[value(Class)] = {str(Class)}
                else:
                    td[value(Class)].add(str(Class))
        return {key: td[key] for key in sorted(td.keys())} # sort topological dict for readability
    else:
        unsat_core = vmodel
        return unsat_core

def find_incomplete_preferences(file_name):
    bsat, bmodel = solve_consistency(file_name)
    if not bsat:
        return bmodel
    # can assume we now have a model
    Classes_list = []
    for i in range(len(bmodel)):
        if isinstance(bmodel[bmodel[i]], z3.ExprRef):
            source_str_name = str(bmodel[i])
            Classes_list.append(z3.Const(source_str_name, ClassSort))
    incomplete_prefs = []
    for class1 in Classes_list:
        for class2 in Classes_list:
            for class3 in Classes_list:
                if str(class1) != str(class2) and str(class2) != str(class3) and str(class1) != str(class3):
                    incompleteness_inst = z3.And(is_better_than(class2,class3)==1,
                                                    is_better_than(class1,class2)==0,
                                                    is_better_than(class2,class1)==0,
                                                    is_better_than(class1,class3)==0,
                                                    is_better_than(class3,class1)==0,)
                    if bmodel.evaluate(incompleteness_inst):
                        incomplete_prefs.append((class1, class2, class3))
    return incomplete_prefs            

def print_incomplete_preferences(file_name):
    incomplete_preferences = find_incomplete_preferences(file_name)
    if not incomplete_preferences:
        print("there are no incomplete preferences")
    # can assume there are incomplete preferences
    for c1, c2, c3 in incomplete_preferences:
        print(f"\t{c2}\n{c1}\t  v\n\t{c3}\n\n")
    return len(incomplete_preferences)


# NOTE: DON'T CHANGE NAME OF THESE. OTHER FILE DEPENDS ON THEM
preferences_file = current_dir+'/data/preferences.csv'
expectations_file = current_dir+'/data/expectations.csv'
# CURRENT_FILE_CHECKING can change tho
CURRENT_FILE_CHECKING = preferences_file

# STEP 2: run this block (you can run it even if you haven't filled any of the csv out)
print(f"CURRENT FILE: {CURRENT_FILE_CHECKING}")
result = find_topological_order(CURRENT_FILE_CHECKING)
if not isinstance(result, dict):
    print(result)
else:
    print("data is self-consistent!")
print(result)

new_comparisons = ""
counter = 0
for key in result:
    for class1 in result[key]:
        for class2 in result[key]:
            if class1 != class2 and f"{class2},{class1}," not in new_comparisons:
                new_comparisons += f"{class1},{class2},\n"
                counter += 1
print(new_comparisons)
print(counter)
# print(print_incomplete_preferences(CURRENT_FILE_CHECKING))
    
