from z3 import *
f = open("dependencySet.out","r")
#OutputListFormat following will have a List of Lists eg [[12 23 53],[23,64,35],[345,554,545,84]]
OutputListFormat = list()

#prepopulate outputlistFormat with empty lists
for i in range(10):
	OutputListFormat.insert(i,list())

inputDependencySet = []
# declare two lists for inter-thread dependencies
hbFrom = list()
hbTo = list()

if f.mode == "r":
	inputDependencySet = f.readlines() # read in all the dependency pairs
	for inputLine in inputDependencySet:
		dependencyArray = inputLine.split("-")

		#populate the hb lists above		
		hbFrom.append(int(str(int(dependencyArray[0]) + 1) + str(dependencyArray[1])))
		hbTo.append(int(str(int(dependencyArray[2]) + 1) + str(dependencyArray[3])))

		#inset event(threadid, instruction count into thread's list)
		OutputListFormat[int(dependencyArray[0])].append(int(dependencyArray[1]))		
		OutputListFormat[int(dependencyArray[2])].append(int(dependencyArray[3]))	

f.close();

#clean up OutputListFormat for empty indexes (for traces with threads less than 10)
dellist = list()
z = 0
for i in range(len(OutputListFormat)):
	if not OutputListFormat[i]:
		dellist.insert(z,i)
	z = z + 1
del OutputListFormat[dellist[0]:]
del dellist
#List threads' events created in OutputListFormat
#and remove duplicate events in each thread's list and sort them
#trace contains every unique event from every thread
#in the trace

originalTrace = list()
for a in range(len(OutputListFormat)):
	OutputListFormat[a] = list(dict.fromkeys(OutputListFormat[a]))
	OutputListFormat[a].sort()
	for b in OutputListFormat[a]:
		originalTrace.append(int(str(int(a+1)) + str(b)))

del OutputListFormat
#originalTrace contains all unique events in record trace

hbLength = len(hbFrom)
traceLength = len(originalTrace)

#declare Integer lists in z3 based from formatted data
hbFrom1 = [Int('%i' % i) for i in hbFrom]
hbTo1 = [Int('%i' % j) for j in hbTo]
originalTrace1 = [Int('%i' % k) for k in originalTrace]

# Get list of unique postions for every event in trace output
originalTracePositions = [Int('%i' % l) for l in range(traceLength)]

#create solver using Inter difference logic and add assert constraints
s = SolverFor("QF_IDL")

#ensure trace indexes stay within range of tracelength
for i in range(traceLength):
	s.add(originalTracePositions[i] >= 0, originalTracePositions[i] <= (traceLength-1))

#ensure the positions in final trace are distinct
s.add(Distinct(originalTracePositions))

#assert intra-thread dependencies for all threads
for i in range(traceLength):
	#get first index of event pairs and 
	#check if they match(means from the same thread)
	if i + 1 < traceLength and str(originalTrace[i])[0] == str(originalTrace[i+1])[0]:
		s.add(originalTracePositions[originalTrace1.index(originalTrace1[i])] < originalTracePositions[originalTrace1.index(originalTrace1[i+1])])

#assert inter-thread dependencies
for m in range(hbLength):
	s.add(originalTracePositions[originalTrace1.index(hbFrom1[m])] < originalTracePositions[originalTrace1.index(hbTo1[m])])

noOfTraces = 0
while s.check() == sat:
    noOfTraces += 1
    mod = s.model()
    # The positions
    pp = [mod.eval(p).as_long() for p in originalTracePositions]

    # Print trace suggestion 
    print [originalTrace1[j] for i in range(traceLength) for j in range(traceLength) if pp[j] == i]

    # Add this trace as an assertion to solver 
    s.add(Or([originalTracePositions[i] != mod.eval(originalTracePositions[i]) for i in range(traceLength)]))
    print
    
print "Number of distinct traces= ", noOfTraces