import matplotlib.pyplot as plt
import numpy as np
from classes_ranker import (find_topological_order, 
                            preferences_file,
                            expectations_file)



pref_values = find_topological_order(preferences_file)
exp_values = find_topological_order(expectations_file)
inverted_order=True


def find_var_val(label, var_values):
    for var_val in var_values:
        if label in var_values[var_val]:
            return var_val
    raise ValueError

def find_coordinates(var1_values, var2_values, inverted_order=False):
    """
    var1 labels are a subset of var2 labels
    """
    points = dict()
    for var1_val in var1_values:
        for label in var1_values[var1_val]:
            if inverted_order:
                points[label] = (find_var_val(label, var2_values), var1_val)
            else:
                points[label] = (var1_val, find_var_val(label, var2_values))
    return points
            
points = find_coordinates(pref_values, exp_values, inverted_order) # CHANGE INV_ORDER ABOVE

# Extracting x and y values
x_values = [coord[0] for coord in points.values()]
y_values = [coord[1] for coord in points.values()]

# Create the plot
plt.figure(figsize=(8, 6))
plt.scatter(x_values, y_values, color='blue')

# Add labels to each point
for label, (x, y) in points.items():
    plt.text(x, y, label, fontsize=8, ha='right', va='bottom')



x_line = np.linspace(0, max(x_values) + 1, 100)  # Generate x values from 0
y_line = ((max(y_values)-1)/(max(x_values)-1)) * x_line  # Example line equation y = 2x
plt.plot(x_line, y_line, color='green', linestyle='--', label="y = 2x")

plt.xlim(0, max(x_values)+2)  # X-axis from 0 to 10
plt.ylim(0, max(y_values)+2)  # Y-axis from 0 to 10

# Formatting the graph
xl,yl = "Expectations","Preferences" if inverted_order else "Preferences,Expectations"
plt.xlabel(xl)
plt.ylabel(yl)
plt.title("Graph of Relative Preferences and Expectations for Classes")
plt.grid(True)

# Show the plot
plt.show()