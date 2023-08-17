from z3 import *
import numpy as np
import sys

n = 0			#Size of the grid
limit = 0		#Limit
count = 0		#Line count
num = 0		#Number of cars

startx = 0		#Starting x coordinate of the red car
starty = 0		#Starting y coordinate of the red car

data = []		#Storing the data read from the file
types = [] 		#Type of each car

solver = Solver()

def conjunction(array, length):
	if length == 1:
		return array[0]
	else:
		result = And(array[0], array[1])
		for i in range(2, length):
			result = And(result, array[i])
		return result

def disjunction(array, length):
	if length == 1:
		return array[0]
	else:
		result = Or(array[0], array[1])
		for i in range(2, length):
			result = Or(result, array[i])
		return result

minesCount = 0								#Number of mines
with open(sys.argv[1]) as f:
	for line in f:
		tempData = line.strip().split(',')
		if count == 0:						#First line
			n = (int)(tempData[0])
			limit = (int)(tempData[1])
		elif count == 1:					#Second line
			startx = (int)(tempData[0])
			starty = (int)(tempData[1])
		else:							#Remaining lines(includes both cars and mines)
			for i in range(3):
				tempData[i] = (int)(tempData[i])
			if (tempData[0] == 2):
				minesCount +=1
			data.append(tempData)		
		count = count + 1
num = count-2-minesCount
#pp(data)

mines = [ [0 for i in range(n)] for j in range(n) ]
rposx = [ Int("rx_%s" % (i)) for i in range(limit+1) ]				#x coordinate of the red car after each step
rposy = [ Int("ry_%s" % (i)) for i in range(limit+1) ]				#y coordinate of the red car after each step
posx = [ [Int("cx_%s_%s" % (i, j)) for j in range(num)] for i in range(limit+1) ]	#x coordinate of each car at each step
posy = [ [Int("cy_%s_%s" % (i, j)) for j in range(num)] for i in range(limit+1) ]	#y coordinate of each car at each step

rmove = [ Bool("rm_%s" % (i)) for i in range(limit) ]				#Keeping track of the movement of the red car at each step
move = [ [Bool("m_%s_%s" % (i, j)) for j in range(num)] for i in range(limit) ]	#Keeping track of which car moved at each step

solved = [ Bool("solved_%s" % (i)) for i in range(limit+1) ]				#Keeps track of whether the game has been solved at a particular step

obs = [ [ [Bool("ob_%s_%s_%s" % (i, j, k) ) for k in range(n)] for j in range(n)] for i in range(limit+1)]	#Obstacles at each step
dummy = [ [ [False for k in range(n)] for j in range(n) ] for i in range(limit+1)]				#Dummy variable for initializing obstacles

change = [ [ [Int("ch_%s_%s_%s" % (i, j, k)) for k in range(2)] for j in range(2)] for i in range(limit) ]	#Keeps track of changes at each step

carCount = 0									#Variable to iterate over number of cars
solver.add(rposx[0] == startx)						#Initial x coordinate of the red car
solver.add(rposy[0] == starty)						#Initial y cooordinate of the red car
solver.add(obs[0][startx][starty])						#Obstacles at the location of the red car
solver.add(obs[0][startx][starty+1])						
dummy[0][startx][starty] = True
dummy[0][startx][starty+1] = True

for row in data:						#Getting the data
	dummy[0][row[1]][row[2]] = True			#Initial obstacles		
	if row[0] == 2:
		mines[row[1]][row[2]] = 1			#Identify all the mines
	else:
		solver.add(posx[0][carCount] == row[1])			#Initial x coordinates of all the cars
		solver.add(posy[0][carCount] == row[2])			#Initial y coordinates of all the cars
		types.append(row[0])						#Type of each car(Horizontal or vertical)
		carCount += 1				
		if row[0] == 1:
			dummy[0][row[1]][row[2]+1] = True
		else:
			dummy[0][row[1]+1][row[2]] = True


for i in range(n):
	for j in range(n):
		solver.add( obs[0][i][j] == dummy[0][i][j] )

solver.add(solved[limit])							#Game must be solved after the limit

for s in range(limit):
	solver.add( Implies(solved[s], solved[s+1]) )
	solver.add( And( (rposx[s] == startx), (rposy[s] == n-2) ) == solved[s] )
solver.add( And( (rposx[limit] == startx), (rposy[limit] == n-2) ) == solved[limit] )	

for j in range(starty+2, n):
	solver.add(Not(mines[startx][j] == 1))				#If there mines in the red car's way, return unsat

#All the cars must always stay within the frame
for s in range(limit+1):
	#solver.add(rposx[s] >= 0)
	solver.add(rposy[s] >= 0)
	#solver.add(rposx[s] <= n-1)
	solver.add(rposy[s] <= n-2)
	if (s < limit):
		solver.add(change[s][0][0] >= -1)
		solver.add(change[s][0][0] <= n-1)
		solver.add(change[s][0][1] >= -1)
		solver.add(change[s][0][1] <= n-1)
		solver.add(change[s][1][0] >= -1)
		solver.add(change[s][1][0] <= n-1)
		solver.add(change[s][1][1] >= -1)
		solver.add(change[s][1][1] <= n-1)
	for car in range(num): 
		if (types[car] == 0):
			solver.add(posx[s][car] >= 0)
			solver.add(posx[s][car] <= n-2)
			#solver.add(posy[s][car] >= 0)
			#solver.add(posy[s][car] <= n-1)
		else:
			#solver.add(posx[s][car] >= 0)
			#solver.add(posx[s][car] <= n-1)
			solver.add(posy[s][car] >= 0)
			solver.add(posy[s][car] <= n-2)

for s in range(limit):
	temp = [(rmove[s])]
	#solver.add( Implies(solved[s], Not(rmove[s])) )
	for i in range(num):
		solver.add( Not(And(rmove[s], move[s][i])) )
		#solver.add( Implies(solved[s], Not(move[s][i])) )
		temp.append( move[s][i] )
		for j in range(i+1, num):
			solver.add( Not(And(move[s][i], move[s][j])) )
	cond = disjunction(temp, len(temp))	
	solver.add( Implies(Not(solved[s]), cond) )
	#solver.add( Implies(solved[s], Not(cond)) )		

for s in range(1, limit+1):
	solver.add(rposx[s] == rposx[s-1])
	cond1 = (rposy[s] == rposy[s-1])
	cond2 = (rposy[s] == (rposy[s-1] - 1) )
	cond3 = (rposy[s] == (rposy[s-1] + 1) )
	nextCond = Or(cond1, cond2, cond3)
	solver.add( Not(cond1) == rmove[s-1]  )
	solver.add(nextCond)
	for i in range(n):
		for j in range(1, n-2):
			temp = []
			for k in range(j+1, n):
				temp.append(Not(obs[s-1][i][k]))
			cond = conjunction(temp, len(temp))
			eq = And((rposx[s-1] == i), (rposy[s-1] == j))
			solver.add( Implies(And(eq, cond), cond3) )
			solver.add( Implies(And(eq, cond3), Not(obs[s-1][i][j+2])) )
			solver.add( Implies(And(eq, cond3), change[s-1][0][0] == i) )
			solver.add( Implies(And(eq, cond3), change[s-1][0][1] == j) )
			solver.add( Implies(And(eq, cond3), change[s-1][1][0] == i) )
			solver.add( Implies(And(eq, cond3), change[s-1][1][1] == j+2) )
			solver.add( Implies(And(eq, cond2), Not(obs[s-1][i][j-1])) )
			solver.add( Implies(And(eq, cond2), change[s-1][0][0] == i) )
			solver.add( Implies(And(eq, cond2), change[s-1][0][1] == j-1) )
			solver.add( Implies(And(eq, cond2), change[s-1][1][0] == i) )
			solver.add( Implies(And(eq, cond2), change[s-1][1][1] == j+1) )
			
					
	for j in range(n):
		eq1 = And( (rposy[s-1] == 0), (rposx[s-1] == j) )
		eq2 = And( (rposy[s-1] == n-2), (rposx[s-1] == j) )
		solver.add( Implies(eq1, Not(cond2)) )
		solver.add( Implies(eq2, Not(cond3)) )
		solver.add( Implies(And(eq1, cond3), Not(obs[s-1][j][2])) )
		solver.add( Implies(And(eq1, cond3), change[s-1][0][0] == j) )
		solver.add( Implies(And(eq1, cond3), change[s-1][0][1] == 0) )
		solver.add( Implies(And(eq1, cond3), change[s-1][1][0] == j) )
		solver.add( Implies(And(eq1, cond3), change[s-1][1][1] == 2) )
		solver.add( Implies(And(eq2, cond2), Not(obs[s-1][j][n-3])) )
		solver.add( Implies(And(eq2, cond2), change[s-1][0][0] == j) )
		solver.add( Implies(And(eq2, cond2), change[s-1][0][1] == n-3) )
		solver.add( Implies(And(eq2, cond2), change[s-1][1][0] == j) )
		solver.add( Implies(And(eq2, cond2), change[s-1][1][1] == n-1) )
		
for car in range(num):
	for s in range(1, limit+1):
		if (types[car] == 0):
			solver.add(posy[s][car] == posy[s-1][car])
			cond1 = (posx[s][car] == posx[s-1][car])
			cond2 = (posx[s][car] == (posx[s-1][car] - 1) )
			cond3 = (posx[s][car] == (posx[s-1][car] + 1) )
			nextCond = Or(cond1, cond2, cond3)
			solver.add(nextCond)
			solver.add( Not(cond1) == (move[s-1][car]) )
			for i in range(1, n-2):
				for j in range(n):
					eq = And((posx[s-1][car] == i), (posy[s-1][car] == j))
					solver.add( Implies(And(eq, cond3), Not(obs[s-1][i+2][j])) )
					solver.add( Implies(And(eq, cond3), change[s-1][0][0] == i) )
					solver.add( Implies(And(eq, cond3), change[s-1][0][1] == j) )
					solver.add( Implies(And(eq, cond3), change[s-1][1][0] == i+2) )
					solver.add( Implies(And(eq, cond3), change[s-1][1][1] == j) )
					solver.add( Implies(And(eq, cond2), Not(obs[s-1][i-1][j])) )
					solver.add( Implies(And(eq, cond2), change[s-1][0][0] == i-1) )
					solver.add( Implies(And(eq, cond2), change[s-1][0][1] == j) )
					solver.add( Implies(And(eq, cond2), change[s-1][1][0] == i+1) )
					solver.add( Implies(And(eq, cond2), change[s-1][1][1] == j) )
					
			for j in range(n):
				eq1 = And( (posx[s-1][car] == 0), (posy[s-1][car] == j) )
				eq2 = And( (posx[s-1][car] == n-2), (posy[s-1][car] == j) )
				solver.add( Implies(eq1, Not(cond2)) )
				solver.add( Implies(eq2, Not(cond3)) )
				solver.add( Implies(And(eq1, cond3), Not(obs[s-1][2][j])) )
				solver.add( Implies(And(eq1, cond3), change[s-1][0][0] == 0) )
				solver.add( Implies(And(eq1, cond3), change[s-1][0][1] == j) )
				solver.add( Implies(And(eq1, cond3), change[s-1][1][0] == 2) )
				solver.add( Implies(And(eq1, cond3), change[s-1][1][1] == j) )
				solver.add( Implies(And(eq2, cond2), Not(obs[s-1][n-3][j])) )
				solver.add( Implies(And(eq2, cond2), change[s-1][0][0] == n-3) )
				solver.add( Implies(And(eq2, cond2), change[s-1][0][1] == j) )
				solver.add( Implies(And(eq2, cond2), change[s-1][1][0] == n-1) )
				solver.add( Implies(And(eq2, cond2), change[s-1][1][1] == j) )
		else:
			solver.add(posx[s][car] == posx[s-1][car])
			cond1 = (posy[s][car] == posy[s-1][car])
			cond2 = (posy[s][car] == (posy[s-1][car] - 1) )
			cond3 = (posy[s][car] == (posy[s-1][car] + 1) )
			nextCond = Or(cond1, cond2, cond3)
			solver.add( Not(cond1) == (move[s-1][car]) )
			solver.add(nextCond)
			for i in range(n):
				for j in range(1, n-2):
					eq = And((posx[s-1][car] == i), (posy[s-1][car] == j))
					solver.add( Implies(And(eq, cond3), Not(obs[s-1][i][j+2])) )
					solver.add( Implies(And(eq, cond3), change[s-1][0][0] == i) )
					solver.add( Implies(And(eq, cond3), change[s-1][0][1] == j) )
					solver.add( Implies(And(eq, cond3), change[s-1][1][0] == i) )
					solver.add( Implies(And(eq, cond3), change[s-1][1][1] == j+2) )
					solver.add( Implies(And(eq, cond2), Not(obs[s-1][i][j-1])) )
					solver.add( Implies(And(eq, cond2), change[s-1][0][0] == i) )
					solver.add( Implies(And(eq, cond2), change[s-1][0][1] == j-1) )
					solver.add( Implies(And(eq, cond2), change[s-1][1][0] == i) )
					solver.add( Implies(And(eq, cond2), change[s-1][1][1] == j+1) )
					
			for j in range(n):
				eq1 = And( (posy[s-1][car] == 0), (posx[s-1][car] == j) )
				eq2 = And( (posy[s-1][car] == n-2), (posx[s-1][car] == j) )
				solver.add( Implies(eq1, Not(cond2)) )
				solver.add( Implies(eq2, Not(cond3)) )
				solver.add( Implies(And(eq1, cond3), Not(obs[s-1][j][2])) )
				solver.add( Implies(And(eq1, cond3), change[s-1][0][0] == j) )
				solver.add( Implies(And(eq1, cond3), change[s-1][0][1] == 0) )
				solver.add( Implies(And(eq1, cond3), change[s-1][1][0] == j) )
				solver.add( Implies(And(eq1, cond3), change[s-1][1][1] == 2) )
				solver.add( Implies(And(eq2, cond2), Not(obs[s-1][j][n-3])) )
				solver.add( Implies(And(eq2, cond2), change[s-1][0][0] == j) )
				solver.add( Implies(And(eq2, cond2), change[s-1][0][1] == n-3) )
				solver.add( Implies(And(eq2, cond2), change[s-1][1][0] == j) )
				solver.add( Implies(And(eq2, cond2), change[s-1][1][1] == n-1) )

for s in range(limit):
	solver.add( Implies(solved[s], And(change[s][0][0] == -1, change[s][0][1] == -1, change[s][0][1] == -1, change[s][0][1] == -1)) )
for s in range(1, limit+1):
	for i in range(n):
		for j in range(n):
			cl1 = And(change[s-1][0][0] == i, change[s-1][0][1] == j)
			cl2 = And(change[s-1][1][0] == i, change[s-1][1][1] == j)
			solver.add( Or(cl1, cl2) == Not(obs[s][i][j] == obs[s-1][i][j]) )				


result = solver.check()
m = solver.model()
if (result == sat):
	for i in range(limit):
		if (m[solved[i]] == False):
			x1 = (int)(m[change[i][0][0]].as_long())
			y1 = (int)(m[change[i][0][1]].as_long())
			x2 = (int)(m[change[i][1][0]].as_long())
			y2 = (int)(m[change[i][1][1]].as_long())
			print( str((int)((x1+x2)/2)) + ", " + str((int)((y1+y2)/2)) )
else:
	print("unsat")
