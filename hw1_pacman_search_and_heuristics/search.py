# search.py
# ---------
# Licensing Information:  You are free to use or extend these projects for
# educational purposes provided that (1) you do not distribute or publish
# solutions, (2) you retain this notice, and (3) you provide clear
# attribution to UC Berkeley, including a link to http://ai.berkeley.edu.
# 
# Attribution Information: The Pacman AI projects were developed at UC Berkeley.
# The core projects and autograders were primarily created by John DeNero
# (denero@cs.berkeley.edu) and Dan Klein (klein@cs.berkeley.edu).
# Student side autograding was added by Brad Miller, Nick Hay, and
# Pieter Abbeel (pabbeel@cs.berkeley.edu).


"""
In search.py, you will implement generic search algorithms which are called by
Pacman agents (in searchAgents.py).
"""

import util

class SearchProblem:
    """
    This class outlines the structure of a search problem, but doesn't implement
    any of the methods (in object-oriented terminology: an abstract class).

    You do not need to change anything in this class, ever.
    """

    def getStartState(self):
        """
        Returns the start state for the search problem.
        """
        util.raiseNotDefined()

    def isGoalState(self, state):
        """
          state: Search state

        Returns True if and only if the state is a valid goal state.
        """
        util.raiseNotDefined()

    def getSuccessors(self, state):
        """
          state: Search state

        For a given state, this should return a list of triples, (successor,
        action, stepCost), where 'successor' is a successor to the current
        state, 'action' is the action required to get there, and 'stepCost' is
        the incremental cost of expanding to that successor.
        """
        util.raiseNotDefined()

    def getCostOfActions(self, actions):
        """
         actions: A list of actions to take

        This method returns the total cost of a particular sequence of actions.
        The sequence must be composed of legal moves.
        """
        util.raiseNotDefined()


def tinyMazeSearch(problem):
    """
    Returns a sequence of moves that solves tinyMaze.  For any other maze, the
    sequence of moves will be incorrect, so only use this for tinyMaze.
    """
    from game import Directions
    s = Directions.SOUTH
    w = Directions.WEST
    return  [s, s, w, s, w, w, s, w]

# I tried to stick with the pseudocode provided
# In DFS i was forced to move the goal check outside the successor
# loop because the autograder did not like it, despite working and
# expanding less nodes
def depthFirstSearch(problem):
    state = problem.getStartState()
    frontier = util.Stack()
    frontier.push((state,[]))
    explored = set()

    while not frontier.isEmpty():
        state, path = frontier.pop()

        if problem.isGoalState(state):
            return path

        explored.add(state)
        succ = problem.getSuccessors(state)
        for s in succ:
            if s[0] not in explored:
                frontier.push( (s[0], path + [s[1]]) )
    return [] # Failure


def breadthFirstSearch(problem):
    state = problem.getStartState()
    frontier = util.Queue()
    frontier.push((state,[]))
    # An extra explored set, to ensure no duplicates of nodes that are in
    # the frontier but not yet expanded(added to explored). Used set for O(1)
    # A small waste of memory, in bigger applications a cleaner 
    # implementation would be required
    frontierBuf = set() 
    explored = set()
    
    while not frontier.isEmpty():
        state, path = frontier.pop()
        
        if problem.isGoalState(state):
            return path
        
        explored.add(state)
        succ = problem.getSuccessors(state)
        for s in succ:
            # Ensure it is not already explored or currently in frontier
            if s[0] not in explored and s[0] not in frontierBuf:
                frontier.push( (s[0],  path + [s[1]]) )
                frontierBuf.add(s[0])
    return [] # Failure

# Reconstructs the path based on the given dictionary
def reconstructPath(problem, goal, parentDic):
    path = []
    state = goal
    goal = problem.getStartState()

    # Backtrack from parent to parent until you reach the start state
    while state!=goal:
        data=parentDic[state]
        parent=data[0]
        move=data[1]
        path.append(move)
        state=parent

    # Since we reconstruct the path backwards, we need to reverse it
    # to get the correct order of nodes
    path.reverse()

    return path


def uniformCostSearch(problem):
    state = problem.getStartState()
    frontier = util.PriorityQueue()
    frontier.push(state, 0)
    frontierBuf = set()
    explored = set()
    # A dictionary  that for each state holds its parent, the move the parent
    # made to reach the state, and the cost of that move (I represent the
    # parent of the initial state as (-1,-1) - impossible state)
    parentDic = {state:[(-1,-1), '',0]}

    while not frontier.isEmpty():
        state = frontier.pop()

        if problem.isGoalState(state):
            return reconstructPath(problem, state, parentDic)

        explored.add(state)
        succ = problem.getSuccessors(state)
        for s in succ:
            # The total cost to reach to the successor node
            cost = parentDic[state][2]+s[2] 
            if s[0] not in explored and s[0] not in frontierBuf:
                frontier.push(s[0], cost)
                frontierBuf.add(s[0])
                parentDic[s[0]]=[ state, s[1], cost ]
            else: # In case a path to this node already exists, update it if nessesary
                # The currently stored cost for this successor
                fcost = parentDic[s[0]][2]
                if fcost > cost: # If we find a better path-lower cost, update the dictionary
                    parentDic[s[0]]=[ state, s[1], cost ]
                    frontier.update(s[0],cost)
    return [] # Failure


def nullHeuristic(state, problem=None):
    """
    A heuristic function estimates the cost from the current state to the nearest
    goal in the provided SearchProblem.  This heuristic is trivial.
    """
    return 0


def aStarSearch(problem, heuristic=nullHeuristic):
    state = problem.getStartState()
    frontier = util.PriorityQueue()
    frontier.push(state, heuristic(state,problem))
    frontierBuf = set()
    explored = set()
    parentDic = {state:[(-1,-1), '',heuristic(state,problem)]}

    while not frontier.isEmpty():
        state = frontier.pop()

        if problem.isGoalState(state):
            return reconstructPath(problem, state, parentDic)

        explored.add(state)
        succ = problem.getSuccessors(state)
        for s in succ:

            # Calc the heuristic value of the successor
            her = heuristic(s[0],problem)
            # Add it to the cost to take it into account when making a move
            cost = parentDic[state][2]+s[2]+her

            if s[0] not in explored and s[0] not in frontierBuf:
                frontier.push(s[0], cost)
                frontierBuf.add(s[0])
                # The heuristic is not part of the path length, its just used
                # for making decisions, so deduct it
                parentDic[s[0]]=[ state, s[1] , cost-her]
            else:
                fcost = parentDic[s[0]][2]
                if fcost > cost:
                    parentDic[s[0]]=[ state, s[1], cost-her ]
                    frontier.update(s[0],cost)
    return [] # Failure


# Abbreviations
bfs = breadthFirstSearch
dfs = depthFirstSearch
astar = aStarSearch
ucs = uniformCostSearch
