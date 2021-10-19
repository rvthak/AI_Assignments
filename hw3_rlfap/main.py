# AI Assignment 3 | 2020-2021 | Ioannis Rovithakis sdi1800164

import my_csp # The given AIMA csp with a few changes
import time	  # For timing execution

#______________________________________________________________________
# > Choose one of the tests below to run
# > I also give an estimation of the time it took MAC + dom/wdeg to solve
TEST='2-f24'    # SAT   in ~0.176 sec
#TEST='2-f25'    # UNSAT in ~59.79 sec
#TEST='3-f10'    # SAT   in ~26.74 sec
#TEST='3-f11'    # UNSAT in ~46.25 sec
#TEST='8-f10'    # SAT   in ~42.95 sec
#TEST='8-f11'    # UNSAT in ~68.98 sec
#TEST='14-f27'   # SAT   in ~22.54 sec
#TEST='14-f28'   # UNSAT in more than 1 hour (Use FCBJ for much faster results)
#TEST='6-w2'     # UNSAT in ~0.111 sec
#TEST='7-w1-f4'  # SAT   in ~0.426 sec
#TEST='7-w1-f5'  # UNSAT in ~29.69 sec
#TEST='11'       # SAT   in ~14.12 sec

#______________________________________________________________________
# > Choose the amount of test that will be run
TEST_AMOUNT=5

#______________________________________________________________________
# > Choose one of the testing modes below
MODE='FC'
#MODE='MAC'
#MODE='FC-CBJ'
#MODE='MIN-CON'  

#______________________________________________________________________
# > Choose a method for variable ordering
#VAR_ORD = my_csp.first_unassigned_variable
#VAR_ORD = my_csp.mrv
VAR_ORD = my_csp.dom_wdeg

#______________________________________________________________________
# > Choose a method for value ordering
VAL_ORD = my_csp.unordered_domain_values
#VAL_ORD = my_csp.lcv

#______________________________________________________________________
# > Set the max amount of steps that min-conflicts will do before it terminates
MAX_STEPS=300
#MAX_STEPS=100000 # Default value of csp.py

#______________________________________________________________________
# (You can ignore this part)
VARIABLES_FILE='./rlfap/var' + TEST + '.txt'
DOMAINS_FILE='./rlfap/dom' + TEST + '.txt'
CONSTRAINTS_FILE='./rlfap/ctr' + TEST + '.txt'

if VAR_ORD == my_csp.mrv:
    VAR_ORD_METH = "mrv"
elif VAR_ORD == my_csp.dom_wdeg:
    VAR_ORD_METH = "dom_wdeg"
else:
    VAR_ORD_METH = "first_unassigned_variable"

if VAL_ORD == my_csp.lcv:
    VAL_ORD_METH = "lcv"
else:
    VAL_ORD_METH = "unordered_domain_values"
#______________________________________________________________________

def main():
    printStartBanner();
 
    # Get the input data from the given files
    print("|  (i) Reading Input Files...                                          |")
    variables=getVarInput(VARIABLES_FILE)
    domains=getDomInput(VARIABLES_FILE, DOMAINS_FILE)
    neighbors=getNeibInput(CONSTRAINTS_FILE)
    (constraints, constraints_dict)=getConInput(CONSTRAINTS_FILE)
    print("|  < Input Complete >                                                  |")
 
    # Run the tests
    runTests( MODE, variables, domains, neighbors, constraints, constraints_dict)

    printEndBanner()
    return


def runTests(mode, variables, domains, neighbors, constraints, constraints_dict):

	# Choose the algorithm we will use
	if mode == 'FC':
		fun = my_csp.forward_checking
	elif mode == 'MAC':
		fun = my_csp.mac
	
	printTestingBanner()

	# Init the stat variables
	timeSum = 0
	visitSum = 0
	constrCheckSum = 0
	remainingConfl = []

	# Run 5 times and get the average time for a better representation of each method
	for i in range(1,TEST_AMOUNT+1):

		# Create a csp and initialize it with the given data
		csp = my_csp.CSP(variables, domains, neighbors, constraints, constraints_dict)

		start = time.time()

		if mode == 'FC-CBJ':
			out = my_csp.FC_CBJ(csp, VAR_ORD, VAL_ORD)
		elif mode == 'MIN-CON':
			out = my_csp.min_conflicts(csp, MAX_STEPS)
			remainingConfl.append(len(csp.conflicted_vars(csp.current)))
		else:
			out = my_csp.backtracking_search(csp, VAR_ORD, VAL_ORD, fun)

		elapsed = time.time() - start

		# Update the statistic sums
		timeSum += elapsed
		visitSum += csp.nassigns
		constrCheckSum += csp.constraintCheckCount
		#dict_print(out)
		printResults(out, i,  csp.nassigns, elapsed, csp.constraintCheckCount)

	printAverage(visitSum, constrCheckSum, timeSum)

	if mode == 'MIN-CON':
		printRemaining(remainingConfl)

	return


def printResults(out, no, visited, elapsed, conChecks):

	# Check if the constrains were finally satisfied
	if out is None:
		print("|   %3d   |  %8d     |     %9d     |   %7.3f   |  UNSAT   |" % (no, visited, conChecks, elapsed))
	else:
		print("|   %3d   |  %8d     |     %9d     |   %7.3f   |   SAT    |" % (no, visited, conChecks, elapsed))
		#csp.display(out)
	return


def printAverage(visitSum, constrCheckSum, timeSum):
	print("|_________|_______________|___________________|_____________|__________|")
	print("|         |               |                   |             |          |")
	print("| Average | %12.2f  |    %12.2f   |   %7.3f   |   ---    |" % ((visitSum/TEST_AMOUNT), (constrCheckSum/TEST_AMOUNT), (timeSum/TEST_AMOUNT)))
	print("|_________|_______________|___________________|_____________|__________|")
	return


def printRemaining(remainingConfl):
	leng = len(remainingConfl)
	print("|______________________________________________________________________|")
	print("|                                                                      |")
	print("|  (!) Remaining conflicts when min-conflicts was terminated:          |")
	print("|______________________________________________________________________|")
	print("|         |                                                            |")
	for i in range(0,leng):
		print("|   %3d   |  %5d conflicts remaining                                 |" % (i+1, remainingConfl.pop(0)))
	print("|_________|____________________________________________________________|")
	return


def dict_print(neighbors):
	for key in neighbors:
		print(str(key)+' ', neighbors[key])
	return


def getConInput(fileName):
	
	return init_constraints(fileName)


def init_constraints(fileName):

	# Initialize the constraint checks counter
	constraintChecks=0

	def resetConCount():
		constraintChecks=0
		return

	def getConCount():
		return constraintChecks

	lines = []
	with open(fileName, 'r') as file:
	    lines = file.readlines()
    
    # Create and initialize the constraints dict that will be used by constraints()
    # to check if a given constraint is satisfiable
	constraints_dict = dict()
	for i, line in enumerate(lines): 
		if(i!=0):

			tmp=line.split() 

			if (int(tmp[0]),int(tmp[1])) not in constraints_dict.keys():
				constraints_dict[ (int(tmp[0]),int(tmp[1])) ] = []
				constraints_dict[ (int(tmp[1]),int(tmp[0])) ] = []

			constraints_dict[ (int(tmp[0]),int(tmp[1])) ].append((tmp[2],int(tmp[3])))
			constraints_dict[ (int(tmp[1]),int(tmp[0])) ].append((tmp[2],int(tmp[3])))

	file.close()
	#dict_print(constraints_dict)

	# Check if a given constraint is satisfied
	def constraints(A, a, B, b):

		con = constraints_dict[(A,B)]
		sign = con[0][0]
		dist = con[0][1]

		#print(" Testing if |%d - %d| %s %d" % (a, b, sign, dist))
		if( sign == '='):
			return (abs(a-b)==dist)
		elif( sign == '>'):
			return (abs(a-b)>dist)
		elif( sign == '<'):
			return (abs(a-b)<dist)

		return False

	return (constraints, constraints_dict)


def printTestingBanner():
	print("|______________________________________________________________________|")
	print("|______________________________________________________________________|")
	print("|                                                                      |")
	print("|  (i) Testing using %-8s                                          |" % MODE)
	print("|______________________________________________________________________|")
	print("|                                                                      |")
	print("|  > Testing on problem:        %-30s         |" % TEST)
	print("|  > Amount of test-runs:       %-30d         |" % TEST_AMOUNT)

	if MODE == 'MIN-CON':
		print("|  > Min-conflicts max-steps:   %-10d                             |" % MAX_STEPS)
	else:
		print("|  > Variable ordering method:  %-30s         |" % VAR_ORD_METH)
		print("|  > Value ordering method:     %-30s         |" % VAL_ORD_METH)

	print("|______________________________________________________________________|")
	print("|         |               |                   |             |          |")
	print("|  Test   | Visited nodes | Constraint checks |   Runtime   |  Result  |")
	print("|_________|_______________|___________________|_____________|__________|")
	print("|         |               |                   |             |          |")
	return


def printStartBanner():
	print(" ______________________________________________________________________ ")
	print("|                                                                      |")
	print("|                         - AI Assignment 3 -                          |")
	print("|                   Constraint satisfaction problems                   |")
	print("|                   Radio link frequency assignment                    |")
	print("|______________________________________________________________________|")
	print("|                                                                      |")
	return


def printEndBanner():
	print("|______________________________________________________________________|")
	print("|                                                                      |")
	print("|  (!) All tests completed without errors                              |")
	print("|______________________________________________________________________|")
	return


def getVarInput(fileName):
	print("|  > Reading: %-25s                                |" %(fileName))

	# Open the given file and get its lines
	lines = []
	with open(fileName, 'r') as file:
	    lines = file.readlines()

	# Read the first file line (=The total amount of variables on this file)
	#count = int(lines[0])
	#print('\n > Read ' + str(count) + ' variables\n')

	# The rest of the lines are variables
	variables = []
	for i, line in enumerate(lines): # For each variable line
		if(i!=0):
			tmp=line.split() # Split the string to get the variable
			variables.append( int(tmp[0]) ) # And add the int value in the variable list

	file.close()
	
	#print(variables)
	return variables


def getDomInput(var_fileName, dom_fileName):
	print("|  > Reading: %-25s                                |" %(dom_fileName))

	# Open the given files and get their lines
	var_lines = []
	with open(var_fileName, 'r') as var_file:
	    var_lines = var_file.readlines()

	dom_lines = []
	with open(dom_fileName, 'r') as dom_file:
	    dom_lines = dom_file.readlines()

	# Start with an empty dictionary
	domains = dict()

	# For each variable line
	for i, var_line in enumerate(var_lines): 
		if( i != 0 ): # ignore the first line
			# Split the string to get the variable and its domain
			var_tmp = var_line.split() 

			# Search the domain filr to find that domain
			values = []
			for j, dom_line in enumerate(dom_lines):
				if( j != 0 ): # ignore the first line
					dom_tmp = list(dom_line.split()) # Break the line into a list of strings
					if( int(dom_tmp[0]) == int(var_tmp[1]) ): # Found it
						
						# Remove the first two values = domain id + value count
						dom_tmp.pop(0)
						dom_tmp.pop(0)
						# Add the values on a list	
						dom_tmp = list(map(int, dom_tmp))	# Convert them to ints
						
						# Store the resulting values list to the dictionary
						#print(' Variable ' + str(var_tmp[0]) + ' Domain : ', dom_tmp)
						domains[int(var_tmp[0])] = dom_tmp
	
	var_file.close()
	dom_file.close()
	#print(domains)
	return domains


def getNeibInput(fileName):
	print("|  > Reading: %-25s                                |" %(fileName))

	# Open the given file and get its lines
	lines = []
	with open(fileName, 'r') as file:
	    lines = file.readlines()

	neighbors = dict()
	for i, line in enumerate(lines): 
		if(i!=0):

			tmp = line.split() 

			# Add the second variable id to the first one's dictionary
			if int(tmp[0]) not in neighbors.keys():
				neighbors[int(tmp[0])] = []
			neighbors[int(tmp[0])].append( int(tmp[1]) )

			# Add the first one on the second one's dictionary
			if int(tmp[1]) not in neighbors.keys():
				neighbors[int(tmp[1])] = []
			neighbors[int(tmp[1])].append( int(tmp[0]) )

	file.close()
	#dict_print(neighbors)
	return neighbors


if __name__ == '__main__':
	main()
