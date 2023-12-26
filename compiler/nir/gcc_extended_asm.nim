## GCC Extended asm (GAS) stategments nodes that produces from NIR.
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

import nirinsts, nirlineinfos
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
  
  AsmToken = tuple[sec: int, node: GccAsmNode, det: Det, info: PackedLineInfo]
  AsmContext* = object
    strings*: BiTable[string]

const
  OutputConstraints = {'=', '+'} # Must be in output constraints

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

const
  sections = [
    AsmNodeKind.AsmTemplate,
    AsmOutputOperand,
    AsmInputOperand,
    AsmClobber,
    AsmGotoLabel
  ]
  outputOperandSection = 1
  inputOperandSection = 2
  clobberSection = 3
  gotoLabelSection = 4
  operandSections = {outputOperandSection, inputOperandSection}

type
  TokenizerFlag = enum
    InComment
    InLineComment
    IntelSyntax
    InInjectExpr

  Tokenizer = object
    # We guarantee that a whole line is in the captured in asmTemplate section
    captured: string

    line: int # rel to asm stmt
    col: int

    sec: int
    det: Det = AsmTemplate
    parCnt: int

    # Comments info
    oldChar: char
    flags: set[TokenizerFlag]


using self: var Tokenizer

template yieldCaptured: untyped =
  yield (
    self.sec, 
    self.captured.makeStrValNode(c.strings), 
    self.det,
    PackedLineInfo(0)
  )
  self.captured = ""
  
template maybeYieldCaptured: untyped =
  if self.captured != "": yieldCaptured()

template tokenizeString(self; s: string) =
  for i in  0..<s.len:
    inc self.col
    case s[i]:
    of '/':
      case self.oldChar:
      of '/': incl(self.flags, InLineComment) #"//", it's not supported by normal gas, but cool (// can work without newlines)
      of '*': excl(self.flags, InComment) #"*/"
      of '\n': incl(self.flags, InLineComment) # "/sth in the new line"
      else: discard
    of '*':
      if self.oldChar == '/':
        incl(self.flags, InComment) #"/*"
    of '#', '@': incl(self.flags, InLineComment) # '#' and '@' awkward GAS comments. It makes it not arch specific.
    # how to resolve @ccc ?

    # memory clobber is recomended to use with threads

    of '\n':
      if self.det == AsmTemplate: maybeYieldCaptured
      excl(self.flags, InLineComment)
      inc self.line
      self.col = 0
    
    of '[': self.det = SymbolicName
    of ']':
      if self.det != SymbolicName:
        raiseAssert "expected: ']'"
      yieldCaptured()
      self.det = Constraint

    of '(':
      inc self.parCnt
      incl(self.flags, InInjectExpr)
      yieldCaptured()
      self.det = InjectExpr
      
    of ')':
      dec self.parCnt
      if self.parCnt == 0:
        excl(self.flags, InInjectExpr)
        echo "cap: '", self.captured & "'"
        maybeYieldCaptured

    of ':':
      if self.det == AsmTemplate: maybeYieldCaptured
      self.captured = ""
      inc self.sec
      
      self.det = 
        case self.sec
        of operandSections: Constraint
        of clobberSection: Clobber
        of gotoLabelSection: GotoLabel
        else:
          raiseAssert "Invalid section"

    of ',':
      if self.sec > 0:
        yield (
          self.sec,
          makeEmpty(),
          Delimiter,
          PackedLineInfo.default
        )

    else: discard

    self.oldChar = s[i]
    if (
      s[i] notin {'\n', '\r', '\t', ':', '(', ')', '[', ']', ' ', '/'} or 
      (self.sec == 0 and s[i] == ' ')# and not self.beforeLineContentStart)
    ) and {InLineComment, InComment} * self.flags == {}:
      self.captured.add s[i]

iterator asmTokens*(
  t: Tree, n: NodePos, verbatims: BiTable[string];
  man: LineInfoManager,
  c: var AsmContext
): AsmToken =
  let (_, asmStartLine, leftOffset) = man.unpack(t[n].info) 
  var self = Tokenizer()
  for ch in sons(t, n):
    case t[ch].kind
    of Verbatim:
      let s = verbatims[t[ch].litId]
      self.tokenizeString(s)
    else:
      self.oldChar = '\0' # inject expr instead of old char
      maybeYieldCaptured
      
      yield (
        self.sec,
        ch.makeNodePosNode,
        self.det,
        PackedLineInfo.default
      )
  maybeYieldCaptured

  if self.parCnt > 0:
    raiseAssert "expected: ')'"
  elif self.parCnt < 0:
    raiseAssert "expected: '('"
  
  if InComment in self.flags:
    raiseAssert "Multi-Line comment is not closed"


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

proc parseGccAsm*(t: Tree, n: NodePos; verbatims: BiTable[string]; man: LineInfoManager, c: var AsmContext): GccAsmTree =
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

  for i in asmTokens(t, n, verbatims, man, c):
    when defined(nir.debugAsmParsing):
      echo i

    if i.sec != oldSec:# after
      # next Node
      patch(result, pos)
      pos = prepare(result, sections[i.sec])
      if oldSec in operandSections:
        addLastOperand

    case i.det:
    of AsmTemplate, Clobber, GotoLabel: result.nodes.add i.node
    
    of SymbolicName: symbolicName = i.node
    of Constraint: constraint = i.node
    of InjectExpr: injectExpr.add i.node
    of Delimiter:
      if i.sec in operandSections: addLastOperand
    oldSec = i.sec
  if oldSec in operandSections: addLastOperand
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
