#
# MISC mag - Script Triton pour le Bogus Flow Control d'O-LLVM
# https://triton.quarkslab.com
#

from    triton import *
import  smt2lib

# Adresse des 2 variables utilisees
# pour construire le predicat opaque
X_ADDR = 0x60204C
Y_ADDR = 0x602050

# Liste des basic blocks a examiner
BB_LIST = [
        0x400C9B, 0x400B5D, 0x400B51, 0x4007FA,
        0x4009C3, 0x4009F1, 0x4007F5, 0x4008A8,
        0x4009DE, 0x400816, 0x400CAD, 0x400AAE,
        0x400CB9, 0x400A12, 0x400BF9, 0x400CCC
        ]

# Adresse du pre-dispatcheur
END_BLOCK = 0x400CD3
enabled = False

# Retourne les 2 premieres constantes d'un noeud if
def getStates(node):
    if node.getKind() == IDREF.SMT_AST_NODE.EXTRACT:
        return getStates(node.getChilds()[2])

    if node.getKind() == IDREF.SMT_AST_NODE.ZX:
        return getStates(node.getChilds()[1])

    if node.getKind() == IDREF.SMT_AST_NODE.ITE:
        return (getStates(node.getChilds()[1]), getStates(node.getChilds()[2]))

    if node.getKind() == IDREF.SMT_AST_NODE.BV:
        return node.getChilds()[0].getValue()

    if node.getKind() == IDREF.SMT_AST_NODE.DECIMAL:
        return node.getChilds()[0].getValue()

# Construction des variables symboliques
# a partir des registres contenant X et Y
def cafter(instruction):
    global enabled
    if len(instruction.getOperands()) == 2 and \
            instruction.getOperands()[1].getType() == IDREF.OPERAND.MEM_R and \
            (instruction.getOperands()[1].getMem().getAddress() == X_ADDR or instruction.getOperands()[1].getMem().getAddress() == Y_ADDR):
        reg = instruction.getOperands()[0].getReg()
        convertRegToSymVar(reg.getId(), 64)
        enabled = True
    return


def cbefore(instruction):
    global enabled
    if instruction.getAddress() in BB_LIST:
        print "Dans le basic block", hex(instruction.getAddress())

    if instruction.getAddress() == END_BLOCK and enabled:
        EtatSymId = getRegSymbolicID(IDREF.REG.RAX) # Id de l'expression symbolique
        node = getFullExpression(getSymExpr(EtatSymId).getAst()) # expression complete
        state1, state2 = getStates(node) # Extraction des 2 etats possibles

        expr            = smt2lib.smtAssert(smt2lib.equal(node, smt2lib.bv(state1, 32))) # Solver pour le premier etat
        modelsState1    = getModel(expr)

        expr            = smt2lib.smtAssert(smt2lib.equal(node, smt2lib.bv(state2, 32))) # Solver pour le deuxieme
        modelsState2    = getModel(expr)

        if len(modelsState1) > 0 and len(modelsState2) == 0:        # Pas de solutions pour le 2eme mais une pour le 1er
            print "L'Etat 0x%x ne peut pas etre atteint"%(state2)
        if len(modelsState1) == 0 and len(modelsState2) > 0:
            print "L'Etat 0x%x ne peut pas etre atteint"%(state1)   # Pas de solutions pour le 1er mais une pour le 2eme

        # Reset
        enabled = False
        concretizeAllMem()
        concretizeAllReg()

        return

def fini():
    print "[+] Fin de l'analyse!"


if __name__ == '__main__':

    # Debut de l'analyse a partir de la fonction check
    startAnalysisFromSymbol('check')

    # Definition des callbacks
    addCallback(cafter,         IDREF.CALLBACK.AFTER)
    addCallback(cbefore,        IDREF.CALLBACK.BEFORE)
    addCallback(fini,           IDREF.CALLBACK.FINI)

    runProgram()


