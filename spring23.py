###################################
# CodinGame Spring 2023 Challenge #
# Lounes Mechouek                 #
# 2023/05/26                      #
###################################

import sys
import time
import math
from collections import deque
import heapq
import pandas as pd

#################################
#           Classes             #
#################################
class Balise:
    def __init__(self, idCellule, puissance=0, owner=0):
        self.__puissance = puissance
        self.__idCellule = idCellule
        self.__owner = owner # 0 = Player's | 1 = Opponent's

    def getPuissance(self):
        return self.__puissance
    def getIdCellule(self):
        return self.__idCellule
    def getOwner(self):
        return self.__owner

    def setPuissance(self, puissance):
        self.__puissance = puissance
    def setIdCellule(self, idCellule):
        self.__idCellule = idCellule
    def setOwner(self, owner):
        self.__owner = owner

class Cellule:
    def __init__(self, id, typeCel, initialResources, idsVoisins=[]):
        self.__id = id
        self.__typeCel = typeCel
        self.__initialResources = initialResources
        self.__idsVoisins = idsVoisins
        self.__currentResources = initialResources
        self.__myAntsNumber = 0
        self.__oppAntsNumber = 0
        self.__balise = None

    # Getters
    def getId(self):
        return self.__id
    def getTypeCell(self):
        return self.__typeCel
    def getInitialResources(self):
        return self.__initialResources
    def getIdsVoisins(self):
        return self.__idsVoisins
        return self.__currentResources
    def getMyAntsNumber(self):
        return self.__myAntsNumber
    def getOppAntsNumber(self):
        return self.__oppAntsNumber
    def getBalise(self):
        return self.__balise
    def getCurrentResources(self):
        return self.__currentResources

    # Setters
    def setType(self, typeCel):
        self.__typeCel = typeCel
    def setCurrentResources(self, currentResources):
        self.__currentResources = currentResources
    def setMyAntsNumber(self, myAntsNumber):
        self.__myAntsNumber = myAntsNumber
    def setOppAntsNumber(self, oppAntsNumber):
        self.__oppAntsNumber = oppAntsNumber
    def setBalise(self, puissance, owner=0):
        self.__balise = Balise(self.__id, puissance, owner)
    
class Map:
    def __init__(self, nbBases=1, cellules=[], totalResources={}, playerBaseIdx=[], oppBaseIdx=[]):
        self.__cellules=cellules
        self.__nbBases=nbBases
        self.__playerBaseIdx=playerBaseIdx
        self.__oppBaseIdx=oppBaseIdx
        self.__totalResources = totalResources

    # Getters
    def getCellules(self):
        return self.__cellules
    def getNbBases(self):
        return self.__nbBases
    def getPlayerBaseIdx(self):
        return self.__playerBaseIdx
    def getOppBaseIdx(self):
        return self.__oppBaseIdx
    def getTotalResources(self, typeRessources):
        return self.__totalResources[typeRessources]

    # Setters
    def setNbBases(self, nbBases):
        self.__nbBases = nbBases
    def addCellule(self, cellule):
        if cellule:
            self.__cellules.append(cellule)
    def setCellules(self, cellules):
        if cellules:
            self.__cellules = cellules
    def setPlayerBaseIdx(self, playerBaseIdx):
        self.__playerBaseIdx = playerBaseIdx
    def setOppBaseIdx(self, oppBaseIdx):
        self.__oppBaseIdx = oppBaseIdx
    def setTotalResources(self, typeRessources):
        tr = 0
        for cell in self.__cellules:
            if cell.getTypeCell() == typeRessources:
                tr += cell.getInitialResources()
        self.__totalResources[typeRessources] = tr

    def computeShortestPathBFS(self, idCell1, idCell2):
        fileAtt = deque()
        fileAtt.append((idCell1, []))
        visited = set()
        
        i=0
        while fileAtt:
            idNoeud, path = fileAtt.popleft()

            if idNoeud == idCell2:
                return path+[idNoeud]
            
            visited.add(idNoeud)

            voisins = self.__cellules[idNoeud].getIdsVoisins()
            # on supprime les voisins vides
            voisins = list(filter(lambda x: x != -1, voisins))

            for voisin in voisins:
                if voisin not in visited:
                    fileAtt.append((voisin, path+[idNoeud]))


        print(f"Erreur lors de la recherche du plus court chemin entre {idCell1} et {idCell2}...", file=sys.stderr, flush=True)
        return []

    def __reconstructPathASTAR(self, cameFrom, current):
        totalPath = [current]
        while current in cameFrom:
            current = cameFrom[current]
            totalPath.append(current)
        return totalPath[::-1]

    def computeBestPathASTAR(self, idCell1, idCell2, typeRessource):
        fileAtt = []
        heapq.heappush(fileAtt, (0, idCell1))
        cameFrom = {} # On garde les noeud de provenance pour reconstruire le chemin
        g_scores = {cell.getId(): float('inf') for cell in self.__cellules}
        f_scores = {cell.getId(): float('inf') for cell in self.__cellules}

        # On utilise BFS comme heuristique pour le calcul de la distance entre A et B
        g_scores[idCell1] = 0
        f_scores[idCell1] = len(self.computeShortestPathBFS(idCell1, idCell2))

        while fileAtt:
            _, idNoeud = heapq.heappop(fileAtt)

            if idNoeud == idCell2:
                return self.__reconstructPathASTAR(cameFrom, idNoeud)
            
            voisins = self.__cellules[idNoeud].getIdsVoisins()
            # on supprime les voisins vides
            voisins = list(filter(lambda x: x != -1, voisins))
            for voisin in voisins:
                if self.__cellules[voisin].getTypeCell() == typeRessource:
                    tentativeGScore = g_scores[idNoeud] + self.__cellules[voisin].getCurrentResources()
                else:
                    tentativeGScore = g_scores[idNoeud]

                if tentativeGScore < g_scores[voisin]:
                    cameFrom[voisin] = idNoeud
                    g_scores[voisin] = tentativeGScore
                    f_scores[voisin] = tentativeGScore + len(self.computeShortestPathBFS(voisin, idCell2))
                    heapq.heappush(fileAtt, (f_scores[voisin], voisin))
        
        print("Erreur lors de la recherche du chemin optimal", file=sys.stderr, flush=True)
        return None

class MatchMaking:
    def __init__(self, map=None, focus=[], firstRound=True, myFourmis=[], oppFourmis=[], resourceValues={}, gdTable={}, topHalfIdx={}, bestChemins=[]):
        self.__map=map
        self.__focus=focus 
        self.__myFourmis=myFourmis
        self.__oppFourmis=oppFourmis
        self.__resourceValues=resourceValues
        self.__firstRound=firstRound
        self.__gdTable = gdTable
        self.__topHalfIdx = topHalfIdx
        self.__bestChemins = bestChemins
        
    def getMap(self):
        return self.__map
    def getFocus(self):
        return self.__focus
    def getMoreThanHalf(self):
        return self.__moreThanHalf
    def getMyFourmis(self):
        return self.__myFourmis
    def getOppFourmis(self):
        return self.__oppFourmis
    def getRessourceValues(self, typeRessource):
        return self.__resourceValues[typeRessource]
    def getMaxRessourceValues(self, typeRessource):
        maxValue = max(self.__resourceValues[typeRessource].values())
        return [key for key, value in self.__resourceValues[typeRessource].items() if value == maxValue]
    def getBestChemins(self):
        return self.__bestChemins

    def getRessourceProportions(self, typeRessource):
        valuesProportions = {}

        # S'il n'y a plus de cellules de ce type, on retourne vide
        if typeRessource not in list(self.__resourceValues.keys()):
            return valuesProportions

        for cell in self.__resourceValues[typeRessource].keys():
            valuesProportions[cell] = self.__resourceValues[typeRessource][cell] / self.__map.getTotalResources(typeRessource)
        return {k: v for k, v in sorted(valuesProportions.items(), key=lambda item: item[1], reverse=True)}
    def getNumberFourmis(self):
        return sum(self.__myFourmis)
    def getFirstRound(self):
        return self.__firstRound

    def setMap(self, map):
        self.__map = map
    def setFocus(self, focus):
        self.__focus = focus
    def setMoreThanHalf(self, moreThanHalf):
        self.__moreThanHalf = moreThanHalf
    def setMyFourmis(self, myFourmis):
        self.__myFourmis = myFourmis
    def setOppFourmis(self, oppFourmis):
        self.__oppFourmis = oppFourmis
    def setRessourceValues(self, resourceValues):
            self.__resourceValues = resourceValues
    def setFirstRound(self, firstRound):
        self.__firstRound=firstRound
    def setBestChemins(self, bestChemins):
        self.__bestChemins = bestChemins

    def __computeGainDistance(self, idCell1, idCell2, typeChemin, typeRessource):
        if typeChemin==0: # Shortest
            path = self.__map.computeShortestPathBFS(idCell1, idCell2)
        elif typeChemin==1:
            path = self.__map.computeBestPathASTAR(idCell1, idCell2, typeRessource)
        else:
            print("type de chemin spécifié non reconnu.", file=sys.stderr, flush=True)
            return

        distance = len(path)
        gain = 0
        for idCell in path:
            if self.__map.getCellules()[idCell].getTypeCell() == typeRessource:
                gain += self.__map.getCellules()[idCell].getCurrentResources()
        return path, gain, distance

    def __computeDelai(self, path, fourmisNb):
        '''
            On cherche à estimer le délai de minage des ressources de la cellule d'indice path[len(path)-1]
            Les oeufs influent directement sur la capacité de minage.
        '''
        notEnough = False
        nbFourmisReel = fourmisNb
        gainCristaux = 0
        dicoFourm = {}
        longParcours = 1
        longPath = int(len(path)-1)
        
        cellRes = self.__map.getCellules()[path[longPath]].getCurrentResources()
        while cellRes > 0:
            if longParcours <= longPath:
                if self.__map.getCellules()[path[longParcours]].getTypeCell() == 1:
                    dicoFourm[path[longParcours]] = self.__map.getCellules()[path[longParcours]].getCurrentResources()
                elif self.__map.getCellules()[path[longParcours]].getTypeCell() == 2 :
                    gainCristaux += self.__map.getCellules()[path[longParcours]].getCurrentResources()

            if dicoFourm:
                for cellule in list(dicoFourm.keys()):
                    if nbFourmisReel < min(longParcours, longPath+1): #probleme
                        newFourmis = 0
                        notEnough = True
                        break
                    else:
                        newFourmis = nbFourmisReel // min(longParcours, longPath+1)

                    if dicoFourm[cellule] > newFourmis:
                        dicoFourm[cellule] -= newFourmis
                        nbFourmisReel += newFourmis
                    else:
                        if dicoFourm[cellule] != 0:
                            nbFourmisReel += newFourmis
                        dicoFourm[cellule] = 0
            
            if longParcours > longPath:
                cellRes -= (int(nbFourmisReel) // longPath)

            longParcours+=1    
        
        return longParcours, nbFourmisReel-fourmisNb, gainCristaux, notEnough

    def __computeGDMatrix(self, bases, cellules, typeRessource):
        bestFifty = -1
        i=0
        tableGainDistance = pd.DataFrame(columns=['typeRessource', 'Chemin', 'Type', 'Gain', 'Distance', 'G/D'])
        for baseID in bases:
            for cellID in cellules:
                bfsPath, bfsGain, bfsDistance = self.__computeGainDistance(baseID, cellID, 0, typeRessource)
                astarPath, astarGain, astarDistance = self.__computeGainDistance(baseID, cellID, 1, typeRessource)

                if (bfsGain/bfsDistance) >= (astarGain/astarDistance) and bfsDistance <= self.getNumberFourmis():
                    tableGainDistance.loc[len(tableGainDistance)] = [typeRessource, bfsPath, 'Shortest', bfsGain, bfsDistance, bfsGain/bfsDistance]
                elif (bfsGain/bfsDistance) < (astarGain/astarDistance) and astarDistance <= self.getNumberFourmis():
                    tableGainDistance.loc[len(tableGainDistance)] = [typeRessource, astarPath, 'Optimal', astarGain, astarDistance, astarGain/astarDistance]
                else:
                    break
                
                if typeRessource==2:
                    if (tableGainDistance['Gain'].sum() / self.__map.getTotalResources(typeRessource)) > 0.95 : bestFifty=i
                elif typeRessource==1:
                    if (tableGainDistance['Gain'].sum() / self.__map.getTotalResources(typeRessource)) > 0.5 : bestFifty=i
                i+=1
  
        tableGainDistance = tableGainDistance.sort_values('G/D', ascending=False)
        tableGainDistance.reset_index(drop=True, inplace=True)
        return tableGainDistance, bestFifty

    def __getStrategyPaths(self, typeRessources = [1, 2]):
        '''Renvoie la liste de paths à attaquer dans l'ordre pour maximiser les gains
        typeRessource : spécifier dans l'ordre [indice_oeuf, indice_cristaux]
        '''
        # Nous savons que :
        # A* calcule le chemin qui offre le meilleur gain entre deux cellules A et B (Optimal).
        # BFS calcule le plus court chemin entre deux cellules A et B indépendamment du gain perçu (Shortest).

        # On calcule d'abord les tables de gains-distance entre les bases et les cellules d'intérêt (oeufs/cristaux)
        # |--------------------------------------------------------|
        # | Chemin | Type-Chemin | Gain | Distance | Gain/Distance |
        # |--------------------------------------------------------|
        # | 1->5   | Optimal     | 500  | 5        | 100           |
        # | 1->5   | Shortest    | 150  | 2        | 75            |
        # | 1->3   | Optimal     | 120  | 3        | 40            |
        # | 1->3   | Shortest    | 100  | 2        | 50            |
        # ...etc
        # 
        # On définit la meilleure stratégie :
        # a. Pour les N premiers chemins dont la somme des gains en cristaux est > à 50% des gains :
        #    a.1. Calculer le délai (en nombre de tours) pour récolter ces ressources-ci (soit D1)
        #
        # b1. Pour les M premiers chemins dont la somme des oeufs est > à 50% :
        #    b.1.1. Calculer le délai (en nombre de tours) pour récolter ces ressources-ci
        # b2. Calculer le nouveau délai (en nombre de tours) pour récolter les cristaux avec ce nombre de fourmis (soit D2)
        #
        # Si (D1 > D2) renvoyer les N premiers chemins de cristaux
        # Sinon renvoyer les M chemins d'oeufs + Les N chemins de cristaux
        # 
        # Problème à adresser plus tard : certains chemins pour chercher des oeufs peuvent contenir des cristaux et inversement, il faut inclure cela dans les calculs de délai
        numberFourmis = self.getNumberFourmis()
        noEggs = False
        topHalfPaths = {}

        for i in typeRessources:
            rprop = self.getRessourceProportions(i)
            if rprop:
                if self.__firstRound:
                    self.__gdTable[i], self.__topHalfIdx[i] = self.__computeGDMatrix(self.__map.getPlayerBaseIdx(), list(rprop.keys()), i)

                topHalfPaths[i] = []
                if self.__topHalfIdx[i] != -1:
                    for j in range(self.__topHalfIdx[i]):
                        topHalfPaths[i].append(self.__gdTable[i].loc[j].Chemin)
                else:
                    topHalfPaths[i]=self.__gdTable[i]["Chemin"].tolist()
            else:
                noEggs = True

        if not noEggs:
            # Calcul du chemin optimal
            # A : Chemin sans fourmis additionnelles
            delaiRecord = {}
            otherRessources = {}
            delaiChemin = {}

            delaiRecord[typeRessources[1]] = 0
            otherRessources[typeRessources[1]] = 0
            delaiChemin[typeRessources[1]] = {}
            k=0

            for chm in topHalfPaths[typeRessources[1]]:
                delai, newFourmis, _, tooShort = self.__computeDelai(chm, numberFourmis+otherRessources[typeRessources[1]])       
                delaiRecord[typeRessources[1]] += delai
                otherRessources[typeRessources[1]] += newFourmis
                delaiChemin[typeRessources[1]][k] = delai        
                k+=1
            
            # B : Chemin avec fourmis
            delaiRecord[typeRessources[0]] = 0
            otherRessources[typeRessources[0]] = 0
            delaiChemin[typeRessources[0]] = {}
            fourmisSupp = 0

            ## Cout des fourmis
            j=0
            for chm in topHalfPaths[typeRessources[0]]:
                delai, newFourmis, gainSupp, tooShort = self.__computeDelai(chm, numberFourmis+fourmisSupp)
                delaiRecord[typeRessources[0]] += delai
                otherRessources[typeRessources[0]] += gainSupp
                fourmisSupp += newFourmis
                delaiChemin[typeRessources[0]][j] = delai
                j+=1

            ## Cout des cristaux
            k=0
            otherRessources[typeRessources[1]] = fourmisSupp
            for chm in topHalfPaths[typeRessources[1]]:
                delai, newFourmis, _, tooShort = self.__computeDelai(chm, numberFourmis+otherRessources[typeRessources[1]]) # otherRessources[typeRessources[0]]
                delaiRecord[typeRessources[0]] += delai
                otherRessources[typeRessources[1]] += newFourmis
                delaiChemin[typeRessources[0]][j] = delai
                k+=1
                j+=1
            
            #print(f"\t Chemin 1 : {topHalfPaths[typeRessources[0]]+topHalfPaths[typeRessources[1]]} | Délai 1 : {delaiRecord[typeRessources[0]]}", file=sys.stderr, flush=True)
            #print(f"\t Chemin 2 : {topHalfPaths[typeRessources[1]]} | Délai 2 : {delaiRecord[typeRessources[1]]} ", file=sys.stderr, flush=True)
            
            if delaiRecord[typeRessources[0]] < delaiRecord[typeRessources[1]]: return topHalfPaths[typeRessources[0]]+topHalfPaths[typeRessources[1]]
            else: return topHalfPaths[typeRessources[1]]
        
        else:
            return self.__gdTable[2]['Chemin'].tolist()
                
    def bulletStrategy(self, idRound):
        '''
            L'idée est d'attaquer un chemin à la fois (celui qui offre la meilleure perspective de rapport Gain/Distance)
            Les effectifs (fourmis) sont distribués équitablement sur les cellules du chemin entre la base est la cellule cible
            Le but est de minimiser le temps de minage des cristaux avec des effectifs élevés et de passer d'une cellule contenant des cristaux à l'autre.
            D'où le nom bullet - opération éclair.
        '''  
        equal = False
        cheminsOptimaux = self.__getStrategyPaths()

        if self.__firstRound:    
            # Le chemin
            self.__focus[0] = 0
            # La cellule du chemin
            self.__focus[1] = cheminsOptimaux[self.__focus[0]][len(cheminsOptimaux[self.__focus[0]])-1]
            self.__bestChemins = cheminsOptimaux

        else:
            if cheminsOptimaux != self.__bestChemins:
                self.__focus[0] = 0
                self.__focus[1] = cheminsOptimaux[self.__focus[0]][len(cheminsOptimaux[self.__focus[0]])-1]

            while self.__map.getCellules()[self.__focus[1]].getCurrentResources() == 0 and not equal:
                self.__focus[0] += 1
                if self.__focus[0] >= len(cheminsOptimaux):
                    self.__focus[0] = 0
                    equal = True
                self.__focus[1] = cheminsOptimaux[self.__focus[0]][len(cheminsOptimaux[self.__focus[0]])-1]

        self.__bestChemins = cheminsOptimaux    
        # Appel aux fonctions de jeu
        if self.__focus[0] < len(cheminsOptimaux) and not equal:
            requetes = []
            for cellId in cheminsOptimaux[self.__focus[0]][::-1]:
                
                requetes.append(f"BEACON {str(cellId)} {str(self.getNumberFourmis()//len(cheminsOptimaux[self.__focus[0]]))}")

            print(';'.join(requetes))
        else:
            print("\t PROBLEM OR EQUAL", file=sys.stderr, flush=True)
            print("WAIT")

    def octopusStrategy(self): 
        '''
            Cette stratégie est plus expansionniste que la précédente. 
            Le but est d'attaque plusieurs cibles à la fois, quitte à diviser ses effectifs.
            La stratégie est donc de coloniser de manière tentaculaire le plus de cellules (oeufs et cristaux) que possible.
        '''
        cheminsOptimaux = self.__getStrategyPaths()

        print(f"Chemins : {cheminsOptimaux}", file=sys.stderr, flush=True)
        # Nombre de cellule qu'on peut attaquer en même temps
        simulAttaq = 0
        totalLenPath = 0
        stop = False

        while not stop and simulAttaq < len(cheminsOptimaux):
            totalLenPath += len(cheminsOptimaux[simulAttaq])         
            if self.getNumberFourmis() < totalLenPath:
                stop = True
            else:
                simulAttaq += 1

        equal = simulAttaq*[False]

        if self.__firstRound:    
            for i in range(simulAttaq):
                self.__focus.append([])
                # Le chemin                
                self.__focus[i].append(i)
                # La cellule du chemin
                self.__focus[i].append(cheminsOptimaux[self.__focus[i][0]][len(cheminsOptimaux[self.__focus[i][0]])-1])
            self.__bestChemins = cheminsOptimaux
       
        else:
            for i in range(simulAttaq):
                if i >= len(self.__focus):
                        self.__focus.append([])
                        self.__focus[i].append(i)
                        self.__focus[i].append(cheminsOptimaux[self.__focus[i][0]][len(cheminsOptimaux[self.__focus[i][0]])-1])
                
                if cheminsOptimaux != self.__bestChemins:
                    self.__focus[i][0] = i
                    self.__focus[i][1] = cheminsOptimaux[self.__focus[i][0]][len(cheminsOptimaux[self.__focus[i][0]])-1]

                while self.__map.getCellules()[self.__focus[i][1]].getCurrentResources() == 0 and not equal[i]:
                    self.__focus[i][0] += 1
                    if self.__focus[i][0] >= len(cheminsOptimaux):
                        self.__focus[i][0] = 0
                        equal[i] = True
                    self.__focus[i][1] = cheminsOptimaux[self.__focus[i][0]][len(cheminsOptimaux[self.__focus[i][0]])-1]

        self.__bestChemins = cheminsOptimaux

        requetes = []
        for i in range(simulAttaq):
            if self.__focus[i][0] < len(cheminsOptimaux) and not equal[i]:  
                for cellId in cheminsOptimaux[self.__focus[i][0]][::-1]:                    
                    requetes.append(f"BEACON {str(cellId)} {str(self.getNumberFourmis()//totalLenPath)}")                    
            else:
                print(f"\t PROBLEM OR EQUAL ?", file=sys.stderr, flush=True) 

        if requetes:
            print(';'.join(requetes))
        else:
            print("WAIT")

        

#################################
#      Conditions initiales     #
#################################
# On crée la map
map = Map()
focus = -1
moreThanHalf = False

### Les inputs doivent être lus dans un certain ordre pour que ça fonctionne
# On lit d'abord les cellules
number_of_cells = int(input())

# On construit la map
total_resources = 0
for i in range(number_of_cells):
    cellInfos = [int(j) for j in input().split()]
    total_resources += cellInfos[1]
    newCell = Cellule(i, cellInfos[0], cellInfos[1], cellInfos[2:8])
    map.addCellule(newCell)

map.setTotalResources(2)
map.setTotalResources(1)

## Gérer le cas de n bases plus tard
number_of_bases = int(input())
my_base_index = []
opp_base_index = []
map.setNbBases(number_of_bases)
for i in input().split():
    my_base_index.append(int(i))
for i in input().split():
    opp_base_index = int(i)

map.setPlayerBaseIdx(my_base_index)
map.setOppBaseIdx(opp_base_index)


# On crée la partie
game = MatchMaking()
game.setMap(map)

#################################
#        Boucle de jeu          #
#################################
round=0
while True:
    if round!=0 : game.setFirstRound(False)
    # On récupère les infos en temps réel des cellules et on met à jour les infos de la partie
    resourceValues = {}
    maxResourceIdx = []
    opponentFourmis = list()
    myFourmis = list()
    for i in range(number_of_cells):
        currentCellInfos = [int(j) for j in input().split()]
        map.getCellules()[i].setCurrentResources(currentCellInfos[0])
        map.getCellules()[i].setMyAntsNumber(currentCellInfos[1])
        map.getCellules()[i].setOppAntsNumber(currentCellInfos[2])

        # On garde trace des id des cellules qui contiennent des fourmis adverses
        # Ainsi que les id de toutes les cellules qui contiennent des cristaux
        # Ainsi que les id des cellules qui contiennent le max de cristaux
        opponentFourmis.append(currentCellInfos[2])
        myFourmis.append(currentCellInfos[1])
        ressources = {}
        if currentCellInfos[0] != 0:
            if map.getCellules()[i].getTypeCell() not in list(resourceValues.keys()):
                resourceValues[map.getCellules()[i].getTypeCell()] = {}       
            resourceValues[map.getCellules()[i].getTypeCell()][i] = currentCellInfos[0]

    game.setMyFourmis(myFourmis)
    game.setOppFourmis(opponentFourmis)
    game.setRessourceValues(resourceValues)


    #game.bulletStrategy(round)
    game.octopusStrategy()
    round+=1