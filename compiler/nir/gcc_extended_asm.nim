## GCC Extended asm stategments nodes that produces from NIR.
## It generates iteratively, so parsing doesn't take long

## Asm stategment structure:
## ```nim
## Asm {
##   AsmTemplate {
##     Some asm code
##     SymUse nimInlineVar # `a`
##     Some asm code
##   }
##   AsmOutputOperand {
##     # [asmSymbolicName] constraint (nimVariableName)
##     AsmInjectExpr {symUse nimVariableName} # for output it have only one sym (lvalue)
##     asmSymbolicName # default: ""
##     constraint
##   }
##   AsmInputOperand {
##     # [asmSymbolicName] constraint (nimExpr)
##     AsmInjectExpr {
##       nodeUse nimVariableName
##     } # (rvalue)
##     asmSymbolicName # default: ""
##     constraint
## }
##  AsmClobber {
##    "clobber"
## }
##  AsmGotoLabel {
##    "label" 
## }
## ```

# It can be useful for better asm analysis and 
# easy to use in all nim targets.

import nirinsts
import std / assertions
import .. / ic / bitabs


type
  Det = enum
    AsmTemplate
    SymbolicName
    InjectExpr
    Constraint
    Clobber
    GotoLabel
    Delimiter

  AsmNodeKind* = enum
    # 1 byte
    AsmStrVal # str val
    AsmNodeUse# node pos
    AsmEmpty

    AsmInjectExpr

    AsmTemplate
    AsmOutputOperand
    AsmInputOperand
    AsmClobber
    AsmGotoLabel

  GccAsmNode* = object
    x: uint32
  
  GccAsmTree* = object
    nodes*: seq[GccAsmNode]
  
  AsmToken = tuple[sec: int, node: GccAsmNode, det: Det]
  AsmContext* = object
    strings*: BiTable[string]

const
  LastAtomicValue = AsmEmpty
  NodeKindBits = 8'u32
  NodeKindMask = (1'u32 shl NodeKindBits) - 1'u32

template kind*(n: GccAsmNode): AsmNodeKind = AsmNodeKind(n.x and NodeKindMask)
template operand*(n: GccAsmNode): uint32 = (n.x shr NodeKindBits)

template toX(k: AsmNodeKind; operand: uint32): uint32 =
  uint32(k) or (operand shl NodeKindBits)

proc makeStrValNode(s: string; strings: var BiTable[string]): GccAsmNode =
  GccAsmNode(x: toX(AsmStrVal, uint32(strings.getOrIncl(s))))

proc makeNodePosNode(n: NodePos): GccAsmNode =
  GccAsmNode(x: toX(AsmNodeUse, uint32(n)))

proc emptyNode(kind: AsmNodeKind): GccAsmNode =
  GccAsmNode(x: uint32(kind))

proc makeEmpty(): GccAsmNode =
  emptyNode(AsmEmpty)

iterator asmTokens(
  t: Tree, n: NodePos, verbatims: BiTable[string];
  c: var AsmContext
): AsmToken =
  template addCaptured: untyped =
    yield (
      sec, 
      captured.makeStrValNode(c.strings), 
      det
    )
    captured = ""
  
  template maybeAddCaptured: untyped =
    if captured != "":
      addCaptured()
  
  var sec = 0
  var det: Det = AsmTemplate
  var left = 0
  var captured = ""
  var nPar = 0
  
  # handling comments
  var
    inComment = false # current char in comment(note: comment chars is skipped)
    isLineComment = false
    foundCommentStartSym = false
    foundCommentEndSym = false

  for ch in sons(t, n):
    case t[ch].kind
      of Verbatim:
        let s = verbatims[t[ch].litId]

        for i in 0..s.high:

          # Comments
          if sec > 0 and foundCommentStartSym:
            # "/?"
            if s[i] == '/':
              # "//"
              inComment = true
              isLineComment = true
            elif s[i] == '*':
              # "/*"
              inComment = true
              isLineComment = false
            foundCommentStartSym = false # updates it
          
          if sec > 0 and not foundCommentStartSym and s[i] == '*':
            #"(!/)*"
            foundCommentEndSym = true
          elif sec > 0 and foundCommentEndSym: # "*?"
            if s[i] == '/': # "*/"
              inComment = false
              # delete captured '/'
              captured = ""
              continue
            foundCommentEndSym = false
          if sec > 0 and s[i] == '/': # '/'
            if captured != "/":
              maybeAddCaptured()
            foundCommentStartSym = true
          if sec > 0 and s[i] == '\n' and inComment:
            if not isLineComment: # /* comment \n
              raiseAssert """expected "*/", not "*""" & s[i] & """" in asm operand"""
            inComment = false
            # delete captured '/'
            captured = ""
            continue
          if inComment:
            # skip commented syms
            continue

          # Inject expr parens
          # countParens()

          if s[i] == '(':
            inc nPar
          elif s[i] == ')':
            if nPar > 1:
              captured.add ')'

            dec nPar
          
          if nPar > 1:
            captured.add s[i]
            # no need parsing of expr
            continue

          
          if s[i] == ':':
            # if sec == 0: # det == AsmTemplate
            #   yield (
            #     sec, 
            #     s[left..i - 1].makeStrValNode(c.strings), 
            #     det
            #   )
              
            maybeAddCaptured()
            inc sec
            # inc det
            left = i + 1
              
            captured = ""

            if sec in 1..2:
              # default det for operands
              det = Constraint
            elif sec == 3:
              det = Clobber
            elif sec == 4:
              det = GotoLabel
          
          # elif s[i] == '\n' and sec == 0:
          #   # split the string
          #   maybeAddCaptured()
          #   left = i + 1

          elif sec == 0 and det == AsmTemplate:
            captured.add s[i]

          elif sec > 0:
            case s[i]:
            of '[':
              # start of asm symbolic name
              det = SymbolicName
            
            of ']':
              if det != SymbolicName:
                raiseAssert "expected: ']'"
              
              addCaptured()

              det = Constraint
              # s[capturedStart .. i - 1]
            
            of '(':              
              addCaptured() # add asm constraint
              det = InjectExpr
            
            of ')':
              if det != InjectExpr:
                raiseAssert "expected: ')'"
              
              maybeAddCaptured()
            
            of ',':
              if sec in 1..2:
                det = Constraint
              
              if sec in {3, 4}:
                maybeAddCaptured()
              
              yield (
                sec,
                makeEmpty(),
                Delimiter
              )
            
            # Capture
            # elif sec == 0 and det == AsmTemplate:
            #   # asm template should not change,
            #   # so we don't skip spaces, etc.
            #   captured.add s[i]

            elif (
              det in {
                SymbolicName, 
                Constraint, 
                InjectExpr, 
                Clobber,
                GotoLabel
              } and 
              s[i] notin {' ', '\n', '\t'}
            ): captured.add s[i]
            else: discard

      else:
        left = 0
        if captured == "/":
          continue
        maybeAddCaptured()
        
        yield (
          sec,
          ch.makeNodePosNode,
          det
        )

  if sec == 0:
    # : not specified 
    yield (
      sec, 
      verbatims[t[lastSon(t, n)].litId].makeStrValNode(c.strings), 
      det
    )
  elif sec > 2:
    maybeAddCaptured()
  
  if sec > 4:
    raiseAssert"must be maximum 4 asm sections"

const
  sections = [
    AsmNodeKind.AsmTemplate,
    AsmOutputOperand,
    AsmInputOperand,
    AsmClobber,
    AsmGotoLabel
  ]

proc patch(tree: var GccAsmTree; pos: PatchPos) =
  let pos = pos.int
  let k = tree.nodes[pos].kind
  assert k > LastAtomicValue
  let distance = int32(tree.nodes.len - pos)
  assert distance > 0
  tree.nodes[pos].x = toX(k, cast[uint32](distance))

proc nextChild(tree: GccAsmTree; pos: var int) {.inline.} =
  if tree.nodes[pos].kind > LastAtomicValue:
    assert tree.nodes[pos].operand > 0'u32
    inc pos, tree.nodes[pos].operand.int
  else:
    inc pos

iterator sons*(tree: GccAsmTree; n: NodePos): NodePos =
  var pos = n.int
  assert tree.nodes[pos].kind > LastAtomicValue
  let last = pos + tree.nodes[pos].operand.int
  inc pos
  while pos < last:
    yield NodePos pos
    nextChild tree, pos

proc prepare*(tree: var GccAsmTree; kind: AsmNodeKind): PatchPos =
  result = PatchPos tree.nodes.len
  tree.nodes.add GccAsmNode(x: toX(kind, 1'u32))

template build*(tree: var GccAsmTree; kind: AsmNodeKind; body: untyped) =
  let pos = prepare(tree, kind)
  body
  patch(tree, pos)

proc parseGccAsm*(t: Tree, n: NodePos; verbatims: BiTable[string]; c: var AsmContext): GccAsmTree =
  result = GccAsmTree()
  var
    pos = prepare(result, AsmTemplate)
    oldSec = 0

    # current operand info
    symbolicName = makeStrValNode("", c.strings)
    constraint = emptyNode(AsmStrVal)
    injectExpr: seq[GccAsmNode] = @[]
  
  template addLastOperand =
    result.build AsmInjectExpr: 
      for i in injectExpr:
        result.nodes.add i
    result.nodes.add symbolicName
    result.nodes.add constraint
    
    symbolicName = makeStrValNode("", c.strings)
    constraint = emptyNode(AsmStrVal)
    injectExpr = @[]

  for i in asmTokens(t, n, verbatims, c):
    when defined(nir.debugAsmParsing):
      echo i

    if i.sec != oldSec:
      # next Node
      patch(result, pos)
      if oldSec in {1, 2}:
        result.build sections[oldSec]:
          addLastOperand
      pos = prepare(result, sections[i.sec])
    
    case i.det:
    of AsmTemplate, Clobber, GotoLabel: result.nodes.add i.node
    
    of SymbolicName: symbolicName = i.node
    of Constraint: constraint = i.node
    of InjectExpr: injectExpr.add i.node
    of Delimiter:
      if i.sec in {1, 2}: addLastOperand
    oldSec = i.sec
  if oldSec in {1, 2}: addLastOperand
  patch(result, pos)


# Repr's
proc addRepr(t: GccAsmTree, n: NodePos; r: var string; strings = BiTable[string].default; offset = 0) =
  for i in 1..offset:
    r.add "  "
  
  case t.nodes[n.int].kind:
    of AsmStrVal:
      r.add '"'
      r.add strings[LitId t.nodes[n.int].operand]
      r.add '"'

    of AsmNodeUse: r.add "NodeUse " & $t.nodes[n.int].operand # just a nodepos
    of AsmEmpty: discard
    
    else:
      r.add $t.nodes[n.int].kind
      r.add " {"
      r.add '\n'

      for i in sons(t, n):
        addRepr(t, i, r, strings, offset + 1)
        r.add "\n"
      
      for i in 1..offset: r.add "  "
      r.add "}\n"

proc repr*(t: GccAsmTree; strings = BiTable[string].default): string =
  result = ""
  var i = 0
  while i < t.nodes.len:
    addRepr t, NodePos(i), result, strings
    nextChild t, i
