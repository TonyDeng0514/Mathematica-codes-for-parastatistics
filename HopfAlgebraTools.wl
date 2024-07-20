(* ::Package:: *)

BeginPackage[ "HopfAlgebraTools`"]
 LoadHA::usage="Input name of HA, return HA Data {mul,\[CapitalDelta], \[Eta], \[Epsilon], S, R, Rb}.";
 CheckRep::usage="Check representation \[Rho] of an algebra (mul,\[Eta]).";

 VerifyAlgebra::usage="VerifyAlgebra[mul,\[Eta]] verify unital associative algebra."
 VerifyCoalgebra::usage="VerifyCoalgebra[\[CapitalDelta],\[Epsilon]] verify counital coassociative coalgebra."
 VerifyHAAxioms::usage="VerifyHAAxioms[mul,\[CapitalDelta],\[Eta],\[Epsilon],S] verify the Hopf algebra axioms. ";
 VerifyWHAAxioms::usage="VerifyHAAxioms[mul,\[CapitalDelta],\[Eta],\[Epsilon],S] verify the weak Hopf algebra axioms. ";
 VerifyWeakAntipode::usage=" VerifyWeakAntipode[mul,\[CapitalDelta],\[Eta],\[Epsilon],S] verify the weak antipode axioms.";
 VerifyBAAxioms::usage="VerifyBAAxioms[mul,\[CapitalDelta],\[Eta],\[Epsilon]] verify the bialgebra axioms. ";
 VerifyWBAAxioms::usage="VerifyWBAAxioms[mul,\[CapitalDelta],\[Eta],\[Epsilon]] verify the weak bialgebra axioms. ";
 VerifyPreBAAxioms::usage="VerifyPreBAAxioms[mul,\[CapitalDelta],\[Eta],\[Epsilon]] verify the prebialgebra axioms. ";
 VerifyQuasitriangularity::usage="VerifyQuasitriangularity[mul,\[CapitalDelta],\[Eta],\[Epsilon],R,Rb] verify the quasitriangular bialgebra axioms.";
 \[Rho]Reg::usage = "\[Rho]Reg[mul] gives the regular representation ";
 \[Rho]Regr::usage = "\[Rho]Regr[mul] gives the regular (right) representation ";
 vRegl::usage = "vRegl[\[CapitalDelta]] gives the regular left corepresentation ";
 vRegr::usage = "vRegr[\[CapitalDelta]] gives the regular right corepresentation ";
 HaarIntegral::usage=" HaarIntegral[\[CapitalDelta]] compute the Haar Integral of a semi-simple Hopf algebra.";
 RmatQYBE::usage="RmatQYBE[R,\[Rho]1,\[Rho]2] gives the R-matrix satisfying QYBE R12 R13 R23=R23 R13 R12, constructed out of universal R and reps \[Rho]1, \[Rho]2";
 RmatYBE::usage="RmatYBE[R,\[Rho]] gives the R-matrix satisfying YBE R12 R23 R12=R23 R12 R23, constructed out of universal R and rep \[Rho]";
 Dual::usage="Construct the dual (co)algebra of a (algebra)coalgebra.";
 DualHA::usage="Construct the dual Hopf algebra";
  Begin[ "Private`"]
  SetDirectory[NotebookDirectory[]];
  Needs["TensorTool`"];
  SA=SparseArray;
  LoadHA[HAName_]:=Module[{R,Rb},
  HAfilename=FileNameJoin[{NotebookDirectory[],StringJoin[HAName,"Data.mx"]}];
  Repfilename=FileNameJoin[{NotebookDirectory[],StringJoin[HAName,"Reps.mx"]}];
  Get[Repfilename];
  {mul,\[CapitalDelta], \[Eta], \[Epsilon], S, R, Rb}=Import[HAfilename];
  {mul,\[CapitalDelta], \[Eta], \[Epsilon], S, R, Rb}
  ];
  CheckRep[\[Rho]_,mul_,\[Eta]_]:=Module[{dA=Length[\[Eta]],\[Rho]T,d},
  d=Dimensions[\[Rho]][[1]];
   \[Rho]T=Transpose[\[Rho],2<->3];
   Transpose[ArrayReshape[\[Rho]T.\[Rho]T,{d,dA^2,d}],2<->3]==\[Rho].mul && ArrayReshape[\[Rho].\[Eta],{d,d}]==Id[d]
  ];


VerifyAlgebra[mul_,\[Eta]_]:=Module[{dA=Length@\[Eta],idt},
idt=Id[dA, SparseArray];
(mul.KP[mul,idt]==mul.KP[idt,mul])&&(mul.KP[\[Eta],idt]==mul.KP[idt,\[Eta]])
];
VerifyCoalgebra[\[CapitalDelta]_,\[Epsilon]_]:=Module[{dA=Dimensions[\[Epsilon]][[2]],idt},
idt=Id[dA, SparseArray];
(KP[\[CapitalDelta],idt].\[CapitalDelta]==KP[idt,\[CapitalDelta]].\[CapitalDelta])&&(KP[\[Epsilon],idt].\[CapitalDelta]==KP[idt,\[Epsilon]].\[CapitalDelta])
];

VerifyPreBAAxioms[mul_,\[CapitalDelta]_,\[Eta]_,\[Epsilon]_]:=Module[{dA,idt,m2,\[Tau],Verify\[CapitalDelta]Multiplicative},
dA=Length@\[Eta];
idt=Id[dA, SparseArray];
\[Tau]=\[CapitalPi][dA];
m2=KP[mul,mul].KP[idt,\[Tau],idt];
Verify\[CapitalDelta]Multiplicative=m2.KP[\[CapitalDelta],\[CapitalDelta]]== \[CapitalDelta].mul;
VerifyAlgebra[mul,\[Eta]]&&VerifyCoalgebra[\[CapitalDelta],\[Epsilon]]&&Verify\[CapitalDelta]Multiplicative//FullSimplify
];
Verify\[Eta]\[Epsilon][mul_,\[CapitalDelta]_,\[Eta]_,\[Epsilon]_]:=(\[CapitalDelta].\[Eta]==KP[\[Eta],\[Eta]])&&(\[Epsilon].mul== KP[\[Epsilon],\[Epsilon]]);
VerifyBAAxioms[mul_,\[CapitalDelta]_,\[Eta]_,\[Epsilon]_]:=VerifyPreBAAxioms[mul,\[CapitalDelta],\[Eta],\[Epsilon]]&&Verify\[Eta]\[Epsilon][mul,\[CapitalDelta],\[Eta],\[Epsilon]];
VerifyWBAAxioms[mul_,\[CapitalDelta]_,\[Eta]_,\[Epsilon]_]:=Module[{dA=Length@\[Eta],idt,VerifyWeakunit,VerifyWeakcounit,mm,\[CapitalDelta]\[CapitalDelta]},
\[Tau]=\[CapitalPi][dA];
idt=Id[dA, SparseArray];
\[CapitalDelta]\[CapitalDelta]=KP[\[CapitalDelta],idt].\[CapitalDelta];
mm=mul.KP[mul,idt];
VerifyWeakunit=\[CapitalDelta]\[CapitalDelta].\[Eta]==KP[idt,mul.\[Tau],idt].KP[\[CapitalDelta].\[Eta],\[CapitalDelta].\[Eta]]==KP[idt,mul,idt].KP[\[CapitalDelta].\[Eta],\[CapitalDelta].\[Eta]] //FullSimplify;
VerifyWeakcounit=\[Epsilon].mm== KP[\[Epsilon].mul,\[Epsilon].mul].KP[idt,\[CapitalDelta],idt]==  KP[\[Epsilon].mul,\[Epsilon].mul].KP[idt,\[Tau].\[CapitalDelta],idt]//FullSimplify;
VerifyPreBAAxioms[mul,\[CapitalDelta],\[Eta],\[Epsilon]]&&VerifyWeakunit&&VerifyWeakcounit
];


VerifyWeakAntipode[mul_,\[CapitalDelta]_,\[Eta]_,\[Epsilon]_,S_]:=Module[{dA=Length@\[Eta],\[Epsilon]t,\[Epsilon]s,idt,\[Tau],VerifySAntiAlgebra,VerifySAntiCoalgebra,VerifyWeakSAxioms},
idt=Id[dA, SparseArray];
\[Tau]=\[CapitalPi][dA];
\[Epsilon]t=KP[\[Epsilon].mul.\[Tau],idt].KP[idt,\[CapitalDelta].\[Eta]];
\[Epsilon]s=KP[idt,\[Epsilon].mul.\[Tau]].KP[\[CapitalDelta].\[Eta],idt];
VerifySAntiAlgebra=(S.mul==mul.KP[S,S].\[Tau])&&(S.\[Eta]==\[Eta]);
VerifySAntiCoalgebra=(\[CapitalDelta].S==\[Tau].KP[S,S].\[CapitalDelta])&&(\[Epsilon].S==\[Epsilon]);
VerifyWeakSAxioms=(mul.KP[S,idt].\[CapitalDelta]==\[Epsilon]s)&&(mul.KP[idt,S].\[CapitalDelta]==\[Epsilon]t);
VerifyWeakSAxioms&&VerifySAntiAlgebra&&VerifySAntiCoalgebra
];
VerifyWHAAxioms[mul_,\[CapitalDelta]_,\[Eta]_,\[Epsilon]_,S_]:=VerifyWBAAxioms[mul,\[CapitalDelta],\[Eta],\[Epsilon]]&&VerifyWeakAntipode[mul,\[CapitalDelta],\[Eta],\[Epsilon],S];
VerifyHAAxioms[mul_,\[CapitalDelta]_,\[Eta]_,\[Epsilon]_,S_]:=VerifyBAAxioms[mul,\[CapitalDelta],\[Eta],\[Epsilon]]&&VerifyWeakAntipode[mul,\[CapitalDelta],\[Eta],\[Epsilon],S];


VerifyQuasitriangularity[mul_,\[CapitalDelta]_,\[Eta]_,\[Epsilon]_,R_,Rb_]:=Module[{dA=Length@\[Eta],Rm,Rbm,VerifyRInv,VerifyR\[CapitalDelta]R,VerifyRCE,idt,m2,\[Tau]},
m2:=KP[mul,mul].KP[idt,\[Tau],idt];
idt=Id[dA, SparseArray];
\[Tau]=\[CapitalPi][dA];
Rm=ArrayReshape[R,{dA^2,1}];
Rbm=ArrayReshape[Rb,{dA^2,1}];
VerifyRInv=(m2.KP[Rbm,Rm]==\[CapitalDelta].\[Eta]) &&(m2.KP[Rm,Rbm]==\[Tau].\[CapitalDelta].\[Eta]);
VerifyR\[CapitalDelta]R= m2.KP[\[Tau].\[CapitalDelta],Rm]== m2.KP[Rm,\[CapitalDelta]];
VerifyRCE=(KP[\[CapitalDelta],idt].Rm== KP[idt,KP[idt,mul].KP[\[Tau],idt]].KP[Rm,Rm])&&(KP[idt,\[Tau].\[CapitalDelta]].Rm== KP[KP[mul,idt].KP[idt,\[Tau]],idt].KP[Rm,Rm]);
VerifyRInv&&VerifyR\[CapitalDelta]R&&VerifyRCE//FullSimplify
];
\[Rho]Reg[mul_]:=Module[{dA},
  dA=Dimensions[mul][[1]];
  Transpose[ArrayReshape[mul,{dA,dA,dA}],2<->3]
  ];
\[Rho]Regr[mul_]:=Module[{dA},
  dA=Dimensions[mul][[1]];
  Transpose[ArrayReshape[mul,{dA,dA,dA}],1<->2]
  ];
vRegl[\[CapitalDelta]_]:=Module[{dA},
  (*The regular left corep*)
  dA=Dimensions[\[CapitalDelta]][[2]];
  Transpose[ArrayReshape[\[CapitalDelta],{dA,dA,dA}],1<->3]
  ];
vRegr[\[CapitalDelta]_]:=Module[{dA},
  (*The regular right corep*)
  dA=Dimensions[\[CapitalDelta]][[2]];
  Transpose[ArrayReshape[\[CapitalDelta],{dA,dA,dA}],2<->3]
  ];
Dual[mul_,\[Eta]_]:={Transpose@mul,Transpose@\[Eta]};
DualHA[mul_,\[CapitalDelta]_,\[Eta]_,\[Epsilon]_,S_]:=Transpose/@{\[CapitalDelta],mul,\[Epsilon],\[Eta],S};
HaarIntegral[\[CapitalDelta]_]:=1/Dimensions[\[CapitalDelta]][[2]] Tr[vRegl[\[CapitalDelta]],Plus,2];
RmatQYBE[R_,\[Rho]1_,\[Rho]2_]:=Module[{d1,d2,dA},
{d1,d1,dA}=Dimensions[\[Rho]1];
{d2,d2,dA}=Dimensions[\[Rho]2];
ArrayReshape[Transpose[\[Rho]1.R.Transpose[\[Rho]2,{2,3,1}],2<->3],{d1 d2,d1 d2}]
];
RmatYBE[R_,\[Rho]_]:=Module[{d,dA},
{d,d,dA}=Dimensions[\[Rho]];
RmatQYBE[R,\[Rho],\[Rho]].\[CapitalPi][d]
];


  End[]

  EndPackage[]

