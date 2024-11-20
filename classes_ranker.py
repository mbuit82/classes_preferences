import z3
from random import shuffle
import os
current_dir = os.path.dirname(__file__)

def make_pairs(classes):
    pairs = []
    for class1 in classes:
        for class2 in classes:
            if (class2, class1) not in pairs and class1 != class2:
                pairs.append((class1, class2))
    shuffle(pairs)
    return pairs

def make_classes_csv(classes, file_name, run=True):
    pairs = make_pairs(classes)
    csv_text = ""
    for pair in pairs:
        csv_text += f"{pair[0]},{pair[1]},\n"
    if not run: # run param ensures that preference csv is not overwritten if set to False
        print(f"NOTE: 'run' parameter for make_classes_cv is set to False, so no csv was made")
        return
    # in case you don't set run=False but don't want to overwrite, we have this try block
    try: 
        new_file = open(file_name,'x')
        new_file.write(csv_text)
        new_file.close()
    except:
        overwrite = input(f"file {file_name} already exists. Do you wish to overwrite it? Type Y for yes or any other key for no:")
        if overwrite == 'Y':
            new_file = open(file_name,'w')
            new_file.write(csv_text)
            new_file.close()

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

def process_data(file_name):
    data = get_dsv_text_and_type(file_name)[0]
    data_as_list = data.split('\n')
    processed_data = []
    for row in data_as_list:
        row_as_list = row.split(',')
        assert len(row_as_list) == 3, row_as_list
        if row_as_list[2] != '':
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

# def process_data(file_name):
#     data = get_dsv_text_and_type(file_name)[0]
#     data_as_list = data.split('\n')
#     processed_data = []
#     for row in data_as_list:
#         row_as_list = row.split(',')
#         assert len(row_as_list) == 3, row_as_list
#         processed_data.append(row_as_list)
#     return processed_data

# errmsg = lambda x, y, z: f"the provided preference {z} is not one of the options in comparison ({x}, {y})"

# def make_relations_set(processed_data):
#     relations_set = set()
#     for relation in processed_data: # comparison is a list of 3 strings (representing classes)
#         op1, op2, comparison = relation

#         assert comparison in (op1, op2) or comparison == '-' or comparison == '', errmsg(op1, op2, better_op)
#         if comparison in (op1, op2):
#             worse_op = op1 if comparison == op2 else op2
#             relations_set.add((comparison, worse_op))
#     return relations_set

def solve(solver, constraints):
    result = solver.check(constraints)
    if result == z3.sat:
        return True, solver.model()
    return False, solver.unsat_core()

def find_better(relations_set):
    ClassSort = z3.DeclareSort("ClassSort")
    is_better_than = z3.Function("is_better_than", ClassSort, ClassSort, z3.BitVecSort(1))
    constraints = []
    # for relation in relations_set:
    #     class1_str, class2_str = relation
    #     cs1, cs2 = z3.Const(class1_str, ClassSort), z3.Const(class2_str, ClassSort)
    #     constraints.append(is_better_than(cs1, cs2)==1)
    for relation in relations_set:
        class1_str, class2_str = relation
        cs1, cs2 = z3.Const(class1_str, ClassSort), z3.Const(class2_str, ClassSort)
        constraints.append(is_better_than(cs1, cs2)==1)
        # if comparison_str in (class1_str, class2_str):
        #     worse_op = class1_str if comparison_str == class2_str else class2_str
        #     cs1, cs2 = z3.Const(comparison_str, ClassSort), z3.Const(worse_op, ClassSort)
        #     constraints.append(is_better_than())
    x,y,z = z3.Consts('x y z', ClassSort)
    transitivity = z3.ForAll([x,y,z], z3.Implies(z3.And(is_better_than(x,y)==1, is_better_than(y,z)==1), is_better_than(x,z)==1))
    asymmetry = z3.ForAll([x,y], z3.Implies(is_better_than(x,y)==1, is_better_than(y,x)==0)) # asym (derives reflexivity)
    completeness = z3.ForAll([x,y,z], z3.Implies(is_better_than(y,z)==1,
                                                 z3.Or(is_better_than(x,y)==1,
                                                       is_better_than(y,x)==1,
                                                       is_better_than(x,z)==1,
                                                       is_better_than(z,x)==1,)))
    constraints.append(transitivity)
    constraints.append(asymmetry)
    # constraints.append(z3.Not(completeness))
    bsolver = z3.Solver()
    return solve(bsolver, constraints)

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
                constraints.append(value(Class1) < value(Class2))
    vsolver = z3.Solver()
    return solve(vsolver, constraints)

def find_topological_order(file_name):
    processed_data = process_data(file_name)
    if len(processed_data) == 0:
        return f"no data in the file {file_name} so far"
    relations_set = make_relations_set(processed_data)
    bsat, bmodel = find_better(relations_set)
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
    


# put your classes in this list
classes = ["18.02", "8.01", "24.900", "5.111", "21G.401",
           "18.06", "8.02", "24.902", "21G.402", "6.100L", 
           "6.370", "6.101", "24.951", "24.141", "3.983", 
           "6.390", "24.912", "24.280", "24.952", "6.120", 
           "6.861", "24.970", "24.260", "24.211"]
# put whatever you want the file name and directory to be
file_name = current_dir+'/classes_pairs.csv'

# STEP 1: make the csv file with all class pairs. 
# edit this file so that after each pair (e.g. '18.02,8.01'), put your preference between the two
# (e.g. '18.02,8.01,18.02'). If you have no clear preference, leave it blank (you can also put
# '-', as in '18.02,8.01,-'). This will not ensure the two have the same ranking; it just will
# treat the comparison as if there was not a dash (i.e. it will ignore it)
make_classes_csv(classes, file_name, run=False)

# STEP 2: run this line (you can run it even if you haven't filled any of the csv out)
result = find_topological_order(file_name)
if not isinstance(result, dict):
    print(result)
else:
    print("preferences are self-consistent!")
print(result)
