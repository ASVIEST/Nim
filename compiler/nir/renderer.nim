import std/terminal

type Color = (ForegroundColor, Style)
const
  ResetColors = "\e[0m"
  CommentColor = (fgBlack, styleBright)
  NopColor = (fgWhite, styleDim)
  StrLitColor = (fgYellow, styleDim)
  LabelColor = (fgRed, styleBright)
  IntLitColor = (fgGreen, styleBright)
  TypeColor = (fgCyan, styleDim)
  SymColor = (fgBlue, styleBright)

  ValColor = IntLitColor

proc getColorStr(color: Color): string = color[0].ansiForegroundColorCode & color[1].ansiStyleCode

proc colored(s: string, color: Color): string =
  getColorStr(color) & s & ResetColors

template colored(s: var string, color: Color; body: untyped): untyped =
  var currentColor {.inject.} = color
  s.add color.getColorStr
  body
  s.add ResetColors

template noColor(s: string): string =
  ResetColors & s & getColorStr(currentColor)

import .. / ic / bitabs
import nirinsts, nirtypes

type
  RenderSettings = object
    lineLimit: int

import std/strutils

proc numberConvVal(t: Tree; pos: NodePos; types: TypeGraph; numbers: BiTable[int64]): string =
  result = ""
  let (typ, arg) = sons2(t, pos)
  if t[arg].kind == IntVal:
    let litId = t[arg].litId
    case types[t[typ].typeId].kind
    of UIntTy:
      let x = cast[uint64](numbers[litId])
      result.add $x
    of FloatTy:
      let x = cast[float64](numbers[litId])
      result.add formatFloat(x)
    of BoolTy:
      result.add $bool(numbers[litId])
    else:
      result.add $numbers[litId]
  else: discard

proc hint(s: string): string = colored(" # " & s, CommentColor)

template localName(s: SymId): string =
  let name = names[s]
  if name != LitId(0):
    strings[name]
  else:
    $s.int

template addOffset() =
  r.add repeat(' ', offset * 2 + 2)

template addComplexNode(r: var string; offset: var int; t: Tree, pos: NodePos) =
  r.add $t[pos].kind
  r.add " {\n"
  for p in sons(t, pos):
    addOffset()
    render t, p, strings, integers, names, types, r, offset+1
    r.add '\n'
    
  dec offset
  addOffset()
  r.add "}"

proc render*(
  t: Tree; pos: NodePos;
  strings: BiTable[string], integers: BiTable[int64];
  names: SymNames;
  types: TypeGraph;
  r: var string; # XXX must be out
  offset = 0
) =
  var offset = offset
  case t[pos].kind
  of Nop: r.add colored("Nop", NopColor)
  of StrVal:
    var s = strings[LitId t[pos].rawOperand]
    const lineLimit = 88
        
    if s.len <= lineLimit:
      r.add colored('"' & s & '"', StrLitColor)
    else:
      r.add "StrVal {\n"
      colored(r, StrLitColor):
        var left = 0
        for i in 0..<s.len:
          if i > 0 and i mod lineLimit == 0:
            addOffset()
            escapeToNimLit(s[left..i], r)
            if i < s.len - 1: r.add noColor(" &")
            r.add '\n'
            left = i + 1
        if left != s.len:
          addOffset()
          escapeToNimLit(s[left..^1], r)
          r.add '\n'
      dec offset
      addOffset()
      r.add "}"
  
  of Verbatim:
    const tripleQuote = """""""""
    r.add "Verbatim " & tripleQuote & '\n'
    let s = strings[t[pos].litId]
    r.add s
    r.add '\n'
    dec offset
    addOffset()
    r.add tripleQuote
    
  of ImmediateVal: r.add colored($t[pos].immediateVal, IntLitColor)
  of IntVal:
    r.add "IntVal "
    r.add colored($integers[t[pos].litId], IntLitColor)
  of SymDef:
    r.add "SymDef "
    r.add colored(localName(t[pos].symId), SymColor)
  of SymUse:
    r.add "SymUse "
    r.add colored(localName(t[pos].symId), SymColor)

  of EmitTarget:
    r.add "EmitTarget "
    r.add colored($cast[EmitTargetKind](t[pos].rawOperand), ValColor)
  of PragmaId: r.add colored($cast[PragmaKey](t[pos].rawOperand), ValColor)
  of InfoId:   r.add colored($cast[InfoKey](t[pos].rawOperand), ValColor)

  of NilVal: r.add colored("NilVal", NopColor)
  of Typed:
    r.add colored("T<" & $t[pos].rawOperand & '>', TypeColor)
    r.add hint("kind: " & $types[t[pos].typeId].kind)
  # Hints
  of NumberConv:
    r.addComplexNode(offset, t, pos)
    if types[t[pos.firstSon].typeId].kind != IntTy:
      r.add hint("val: " & numberConvVal(t, pos, types, integers))
  
  of Goto, CheckedGoto, LoopLabel, GotoLoop:
    r.add $t[pos].kind
    r.add ' '
    r.add colored('L' & $t[pos].rawOperand, LabelColor)
  of Label:
    r.add colored('L' & $t[pos].rawOperand, LabelColor)
  else:
    r.addComplexNode(offset, t, pos)

proc renderAllTrees*(
  t: Tree;
  strings: BiTable[string], integers: BiTable[int64];
  names: SymNames;
  types: TypeGraph;
  r: var string;
) =
  var i = NodePos 0
  while i.int < t.len:
    render t, i, strings, integers, names, types, r
    r.add '\n'
    next t, i
