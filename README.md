## Background
This project originated out of curiosity as a way to see if my preferences for the classes I've taken in college are self-consistent. I had a general notion of what classes I liked most and what classes I liked least, but the things in the middle felt like a wash, as if there could easily be a contradiction between (relatively) clear pairwise preferences. I implemented it largely using code I had already written for a separate project (mayanphylogeny) that used Z3 to solve for a topological order of a list of sources for linguistic data given some partial rankings between subsets of them. 

However in a philosophy class we talked about how some value theorists think that preferences can be incomplete (in the sense that given three classes a, b, c, I prefer b to c but have no preference with a to c or a to b). This struck me as odd, and none of the examples in class were immediately convincing to me. So I extended this project to see if my preferences for classes are incomplete (verdict: it seems they are). 

## How to run
First put your classes into the `classes` list in the `make_classes_csv.py` file. This will make a csv file with every single pairwise comparison of classes. Even though not all pairwise comparisons are needed to determine a (complete, never mind partial) order, I figured that giving the opportunity to judge every single pairwise comparison would allow for inconsistencies to more easily show up (harder to "keep track" of what one's judged and let oneself be influenced in this way when one only considers two classes at a time). 

After doing that, run the functions in the `classes_ranker.py` file you're interested in. (Make sure the name of the csv file matches what's in that file!) There are two functions there you can run: 
- `find_topological_order` finds a topological order given preferences. This solves for consistency.
- `print_incomplete_preferences` will find all incomplete preferences (i.e., it will check for every combination of three classes, whether there is a preference between two of them but no preference between each of those and the third) and print them. 
