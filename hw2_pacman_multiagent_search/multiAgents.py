# multiAgents.py
# --------------
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


from util import manhattanDistance
from game import Directions
import random, util

from game import Agent

class ReflexAgent(Agent):
    """
    A reflex agent chooses an action at each choice point by examining
    its alternatives via a state evaluation function.

    The code below is provided as a guide.  You are welcome to change
    it in any way you see fit, so long as you don't touch our method
    headers.
    """


    def getAction(self, gameState):
        """
        You do not need to change this method, but you're welcome to.

        getAction chooses among the best options according to the evaluation function.

        Just like in the previous project, getAction takes a GameState and returns
        some Directions.X for some X in the set {NORTH, SOUTH, WEST, EAST, STOP}
        """
        # Collect legal moves and successor states
        legalMoves = gameState.getLegalActions()

        # Choose one of the best actions
        scores = [self.evaluationFunction(gameState, action) for action in legalMoves]
        bestScore = max(scores)
        bestIndices = [index for index in range(len(scores)) if scores[index] == bestScore]
        chosenIndex = random.choice(bestIndices) # Pick randomly among the best

        "Add more of your code here if you want to"

        return legalMoves[chosenIndex]

    def evaluationFunction(self, currentGameState, action):
        # The values we will need to evaluate the potential action
        successorGameState = currentGameState.generatePacmanSuccessor(action)
        newPos = successorGameState.getPacmanPosition()
        newFood = successorGameState.getFood().asList()
        newGhostStates = successorGameState.getGhostStates()
        newGhostPositions = successorGameState.getGhostPositions()
        newScaredTimes = [ghostState.scaredTimer for ghostState in newGhostStates]
        currentScore = scoreEvaluationFunction(currentGameState)
        newScore = successorGameState.getScore()

        # We want to achieve a high score => Focus on the food as a priority
        # Find the distance from the closest food
        closestFood = float("inf")
        for food in newFood:
            closestFood = min(closestFood, manhattanDistance(newPos, food))

        # We dont wanna get too close to ghosts => Closer than 4 dist = high chance of
        # getting eaten=> avoid at all costs. But if ghosts are scared, take advantage
        # of it and chase them for a higher score if you manage to eat them
        for ghost in newGhostPositions:
            if (manhattanDistance(newPos, ghost) < 4):
                if min(newScaredTimes)>=4: # It has to stay scared for long enough to "catch" it
                    return float('inf')
                return -float('inf')

        # Use reciprocal for food (since the smaller the denominator value of a fraction, the
        # greatest the total value of the fraction => For longer distances the fraction value will fall)
        # Also used the scored gained from this move as a factor (For counting in eating food, ghosts and capsules)
        # I tried a couple of different weights for the return and i used the most effective ones i found
        return 0.8*(newScore-currentScore) + 2.5/closestFood

def scoreEvaluationFunction(currentGameState):
    """
    This default evaluation function just returns the score of the state.
    The score is the same one displayed in the Pacman GUI.

    This evaluation function is meant for use with adversarial search agents
    (not reflex agents).
    """
    return currentGameState.getScore()

class MultiAgentSearchAgent(Agent):
    """
    This class provides some common elements to all of your
    multi-agent searchers.  Any methods defined here will be available
    to the MinimaxPacmanAgent, AlphaBetaPacmanAgent & ExpectimaxPacmanAgent.

    You *do not* need to make any changes here, but you can if you want to
    add functionality to all your adversarial search agents.  Please do not
    remove anything, however.

    Note: this is an abstract class: one that should not be instantiated.  It's
    only partially specified, and designed to be extended.  Agent (game.py)
    is another abstract class.
    """

    def __init__(self, evalFn = 'scoreEvaluationFunction', depth = '2'):
        self.index = 0 # Pacman is always agent index 0
        self.evaluationFunction = util.lookup(evalFn, globals())
        self.depth = int(depth)


class MinimaxAgent(MultiAgentSearchAgent):
# I based this part on the pseudocode from slide 19 of anazitisi_me_antipalotita.pdf
# From http://cgi.di.uoa.gr/~ys02/
        
    def getAction(self, gameState):

        # Max: only pacman agent => always agent==0 
        def maxValue(gameState, depth):
            # We first check if the recursion should continue or not
            # if we have reached a leaf node or the given depth of the problem/test
            # (In a lot of cases for the autograder tests we are given a set depth to work
            # with, to not let minimax expand too many nodes and take too much time to return
            #  a usable result. So we stop it on a set depth and return a sub-optimal result)
            if gameState.isWin() or gameState.isLose() or (depth+1)==self.depth: 
                # Game Over => return the final score
                return self.evaluationFunction(gameState)

            # Get the available moves for pacman
            actions = gameState.getLegalActions(0)

            maxScore = -float("inf")
            # For each available action
            for action in actions:
                # Get the successor state this action leads to
                succ = gameState.generateSuccessor(0,action)
                # Calculate the value of this possible state
                # Call minValue for the first ghost for depth=depth+1
                succScore = minValue(succ, 1, depth+1)
                # Store the greatest score calculated
                maxScore = max(maxScore, succScore)

            # Return the highest score pacma(MAX) can achieve
            return maxScore
        
        def minValue(gameState, agent, depth):

            # We first check if we reached a leaf node - end of recursion
            # Depth only increases on MAX => no need to check it here
            if gameState.isWin() or gameState.isLose(): 
                # Game Over => return the final score
                return self.evaluationFunction(gameState)

            # Get the available moves for the currect ghost
            actions = gameState.getLegalActions(agent)

            minScore = float("inf")
            # For each available action
            for action in actions:
                # Get the successor state this action leads to
                succ = gameState.generateSuccessor(agent, action)

                # Calculate the value of this possible state

                # If the current ghost is not the last ghost 
                if agent!=(gameState.getNumAgents()-1):
                    # Call minValue for the next ghost for depth=depth+1
                    succScore = minValue(succ, agent+1, depth)
                else:
                    # The current ghost is the last ghost playing this turn
                    # Switch to pacman's turn => Call maxValue
                    succScore = maxValue(succ, depth)
                    
                # Store the smallest score calculated
                minScore = min(minScore, succScore)

            # Return the smallest score this ghost(MIN) can achieve
            return minScore
        

        # The main code that gets the available actions of pacman and
        # starts minimax as a max state to evaluate each possible action
        # Returns the action with the greater value for him

        # Get the actions pacman(MAX) has available in the beginning
        actions = gameState.getLegalActions(0)

        maxScore = -float("inf")
        optimalAction = ''
        # For each available action
        for action in actions: 
            # Get the successor state this action leads to
            succ = gameState.generateSuccessor(0,action)
            # Calculate the value of this possible state
            # Call minValue for the first ghost starting from depth 0 
            # (Depth increments only on MAX's turn)
            # (We always have at least one ghost)
            succScore = minValue(succ,1,0)
            # Store the action that leads to the optimal-greatest score
            if succScore > maxScore:
                maxScore = succScore
                optimalAction = action

        return optimalAction


class AlphaBetaAgent(MultiAgentSearchAgent):
# Based on the pseudocode provided on project 2's webpage on Q3, i "upgraded" my code from Q2
# The same comments as minimax apply to the corresponding lines of code,
# i removed them and added some extra for alphaBeta to keep things clean

    def getAction(self, gameState):

        def maxValue(gameState, depth, a, b):

            # We first check if the recursion should continue or not
            if gameState.isWin() or gameState.isLose() or (depth+1)==self.depth: 
                return self.evaluationFunction(gameState)

            # Get the available moves for pacman
            actions = gameState.getLegalActions(0)

            v = -float("inf")
            # For each available action
            for action in actions:
                # Get the successor state this action leads to
                succ = gameState.generateSuccessor(0,action)
                # Calculate the value of this possible state
                v = max(v, minValue(succ, 1, depth+1, a, b))

                # We check the bound set from b. If we find a value bigger than our bound b,
                # there is no point to keep searching, return this value
                # ( For a better explanation on alpha beta logic please read my analytical
                # step-by-step explanation on the theoretical part of the assignment)
                if v>b:
                    return v
                a = max(a,v) # Update the value of a to always store the MAX's best option

            return v

        
        def minValue(gameState, agent, depth, a, b):

            # We first check if we reached a leaf node - end of recursion
            if gameState.isWin() or gameState.isLose(): 
                return self.evaluationFunction(gameState)

            # Get the available moves for the currect ghost
            actions = gameState.getLegalActions(agent)

            v = float("inf")
            # For each available action
            for action in actions:
                # Get the successor state this action leads to
                succ = gameState.generateSuccessor(agent, action)

                # Calculate the value of this possible state

                # If the current ghost is not the last ghost 
                if agent!=(gameState.getNumAgents()-1):
                    v = min(v, minValue(succ, agent+1, depth, a, b))  
                else:
                    # The current ghost is the last ghost playing this turn
                    v = min(v, maxValue(succ, depth, a, b))

                # Same logic as in maxValue, if we find a value smaller than our current bound
                # we stop searching and return it
                if v<a:
                    return v
                b=min(b,v)

            return v
        

        # Initialize a and b to -/+ inf
        a = -float("inf")
        b =  float("inf")

        # Get the actions pacman(MAX) has available in the beginning
        actions = gameState.getLegalActions(0)

        maxScore = -float("inf")
        optimalAction = ''
        # For each available action
        for action in actions: 
            # Get the successor state this action leads to
            succ = gameState.generateSuccessor(0,action)
            # Calculate the value of this possible state
            succScore = minValue(succ,1,0,a,b)
            # Store the action that leads to the optimal-greatest score
            if succScore > maxScore:
                maxScore = succScore
                optimalAction = action

            # Again we handle this part like we handle maxValue since
            # this part of code is a version of maxValue that also includes actions
            if succScore>b:
                return optimalAction
            a = max(a,succScore)

        return optimalAction


class ExpectimaxAgent(MultiAgentSearchAgent):
# I based this part on the pseudocode given on slide 2 of lec-9-6up.pdf and my code from Q2
# https://inst.eecs.berkeley.edu/~cs188/sp20/assets/lecture/lec-9-6up.pdf
# (one of the Berkeley pdf's for this class)
# Like above, the same comments as minimax apply to their corresponding lines of code

    def getAction(self, gameState):

        def maxValue(gameState, depth):

            # We first check if the recursion should continue or not
            if gameState.isWin() or gameState.isLose() or (depth+1)==self.depth: 
                return self.evaluationFunction(gameState)

            # Get the available moves for pacman
            actions = gameState.getLegalActions(0)

            maxScore = -float("inf")
            # For each available action
            for action in actions:
                # Get the successor state this action leads to
                succ = gameState.generateSuccessor(0,action)
                # Calculate the value of this possible state
                maxScore = max(maxScore, expectedValue(succ, 1, depth+1))

            return maxScore
        

        def expectedValue(gameState, agent, depth):

            # We first check if we reached a leaf node - end of recursion
            if gameState.isWin() or gameState.isLose(): 
                # Game Over => return the final score
                return self.evaluationFunction(gameState)

            # Get the available moves for the currect ghost
            actions = gameState.getLegalActions(agent)

            # Each action is a possible move => count them to use for
            # calculating the probabilities later on
            actionCount = len(actions)

            # In v we store the sum of all the score-values of the different actions
            v = 0

            # For each available action
            for action in actions:
                # Get the successor state this action leads to
                succ = gameState.generateSuccessor(agent, action)

                # Calculate the value of this possible state
                # and add all the possible scores up

                # If the current ghost is not the last ghost 
                if agent!=(gameState.getNumAgents()-1):
                    v += expectedValue(succ, agent+1, depth)
                else: # Last Ghost
                    v += maxValue(succ, depth)

            # Divide them by actionCount (Like an average calculation)
            # The distribution of choices is uniform => equal probabilities 
            # for each possible action => 
            # Total possible score = (score_1/actionCount) + ... + (score_actionCount/actionCount)
            # = (score_1 + score_2 + ... + score_actionCount) / actionCount
            return v/actionCount
        

        # We handle the MAX portion of the problem exactly like in minimax, we just need 
        # to make changes on the MIN side, and change it to a  probabilistic action model
        # instead of making deterministic-optimal moves

        # Get the actions pacman(MAX) has available in the beginning
        actions = gameState.getLegalActions(0)

        maxScore = -float("inf")
        optimalAction = ''
        # For each available action
        for action in actions: 
            # Get the successor state this action leads to
            succ = gameState.generateSuccessor(0,action)
            # Calculate the value of this possible state
            succScore = expectedValue(succ,1,0)
            # Store the action that leads to the optimal-greatest score
            if succScore > maxScore:
                maxScore = succScore
                optimalAction = action

        return optimalAction


def betterEvaluationFunction(currentGameState):
# Ideally i would have pre-calculated the manhattan Distances similar to the way 
# i handled the food heuristic from Pacman Project 1, in orded to reduce the run times
# but there was no "dictionary" to use this time, and i was not sure if using a global
# static data structure to store the distances was allowed.
# Like in the first evaluation function, i used reciprocal accordingly to achieve better results
    
    # If we reach a game terminating state, we go for it(or avoid it at all costs accordingly)
    if currentGameState.isWin():
        return float("inf")
    if currentGameState.isLose():
        return -float("inf")

    # The information i decided to use to evaluate this state 
    pacmanPos = currentGameState.getPacmanPosition()
    foodPos = currentGameState.getFood().asList()
    capsulePos = currentGameState.getCapsules()
    ghostPos = currentGameState.getGhostPositions()
    ghostStates = currentGameState.getGhostStates()
    scaredTimes = [ghostState.scaredTimer for ghostState in ghostStates]


    # __ Food gobbling __ ( For a high score we need a good focus in food and speed)
    # Less food in total is better. The closer there is available food the better 
    # The closer we are to the total amount of food on average the best

    # Since i needed both min and sum, i decided to just append all the distances
    # from pacman to food to a list for simplicity
    foodDist = []
    for food in foodPos:
        foodDist.append(manhattanDistance(pacmanPos,food))

    # Get the total amount of food in the game
    foodCount = -len(foodPos)

    # Get the average distance to all, better metric than general distance
    # If foodCount is 0, we have already returned since isWin() returns 1 (No case of div with zero possible)
    foodVal = -foodCount/sum(foodDist) 

    # Get the distance from the closest food
    foodMinDist = 1/min(foodDist)



    # __ Pellet-nabbing __ ( I gave pellets a relatively small priority, I could 
    # improve the system a bit here to achieve an even better score )
    # Less total capsules are better and closest we are to a capsule the better (Better safety) 
    # I ended up not using the total amount of capsules through trial and error tests
    # In most cases it had little to no effect on the result
    capsuleMinDist = 0
    if capsulePos: # If there are any capsules available
        capsuleDist = []
        for capsule in capsulePos:
            capsuleDist.append(manhattanDistance(pacmanPos,capsule))
        capsuleMinDist = 1/min(capsuleDist)


    # __ Ghost-hunting __ ( We need to avoid getting eaten at all costs but at the same time
    # we need a good score, so during scary times go hunting for ghosts)
    # The farther the ghosts the better. If a ghost is in a dangerous distance, check if it
    # is scared or not. If it is, and there is "enough scary time" remaining, try to hunt it
    # down for score points, if not move away to avoid it
    ghostDist = []
    for ghost in ghostPos:
        ghostDist.append(manhattanDistance(pacmanPos,ghost))

    ghostMinDist = min(ghostDist)
    if ghostMinDist < 2:
        if min(scaredTimes) >= 1:
            ghostMinDist = 1000
        else:
            ghostMinDist = -1000
    else:
        ghostMinDist = 1/ghostMinDist

    # Also took into account the score of the state since it adds in the general picture 
    # the score gained by eating food, ghosts or capsules 
    # I played around with the weight values and ended up with these ones. I am sure that
    # with a bit more time somebody can find even better ones
    return 5*currentGameState.getScore() + 4*foodCount + foodMinDist + 2*foodVal + 3*capsuleMinDist +  ghostMinDist 


# Abbreviation
better = betterEvaluationFunction
