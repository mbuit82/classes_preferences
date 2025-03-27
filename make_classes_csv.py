from random import shuffle
import os
current_dir = os.path.dirname(__file__)

def make_pairs(classes, partitions=False):
    pairs = []
    if isinstance(classes[0], list) and partitions == False:
        new_classes = []
        for partition in classes:
            for cls in partition:
                new_classes.append(cls)
        classes = new_classes
    if isinstance(classes[0], str):
        for class1 in classes:
            for class2 in classes:
                if (class2, class1) not in pairs and class1 != class2:
                    pairs.append((class1, class2))
        shuffle(pairs)
    elif isinstance(classes[0], list):
        for partition in classes:
            partition_pairs = []
            for class1 in partition:
                for class2 in partition:
                    if (class2, class1) not in partition_pairs and class1 != class2:
                        partition_pairs.append((class1, class2))
            shuffle(partition_pairs)
            pairs.extend(partition_pairs)
    return pairs

def make_classes_csv(classes, file_name, run=True, partitions=False):
    pairs = make_pairs(classes, partitions=partitions)
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

# TODO: Make an add classes function

# put your classes in this list
classes = [["18.02", "8.01", "24.900", "5.111"], # "21G.401",
           ["18.06", "8.02", "24.902", "21G.402", "6.100L"], 
           ["6.370", "6.101", "24.951", "24.141", "3.983"], 
           ["6.390", "24.912", "24.280", "24.952", "6.120"], 
           ["6.861", "24.970", "24.260", "24.211"],
           ["24.711", "LING216", "6.121", "18.703"]]
# put whatever you want the file name and directory to be
file_name = current_dir+'/expectations/classes_pairs.csv'

# STEP 1: make the csv file with all class pairs. 
# edit this file so that after each pair (e.g. '18.02,8.01'), put your preference between the two
# (e.g. '18.02,8.01,18.02'). If you have no clear preference, leave it blank (you can also put
# '-', as in '18.02,8.01,-'). This will not ensure the two have the same ranking; it just will
# treat the comparison as if there was not a dash (i.e. it will ignore it)
make_classes_csv(classes, file_name, run=True, partitions=True)