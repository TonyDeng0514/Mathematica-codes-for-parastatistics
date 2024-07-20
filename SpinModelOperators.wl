(* ::Package:: *)

BeginPackage[ "SpinModelOperators`"]

  ParaSpinOperators::usage = 
	"ParaSpinOperators[R,nmax] Gives the paraspin operators {Yp,Ym,Xp,Xm,Sp,Sm} corresponding to the R matrix. nmax is the max occupation number on a single site, determined by R."
  CheckXYAlg::usage="CheckXYAlg[R,Yp,Ym,Xp,Xm] checks all the defining relations for the XY algebra."
  CheckYAlg::usage="CheckYAlg[R,Yp,Ym] checks all the defining relations for the Y algebra."
  CheckHerm::usage="CheckHerm[Yp,Ym,Xp,Xm] checks the Hermiticity condition."
  LA::usage="LA[P,Yp,Ym,Xp,Xm] returns the local sl2 generators {E12,E21,n}."
  Begin[ "Private`"]
  SetDirectory[NotebookDirectory[]];
  Needs["TensorTool`"]
  Needs["RMatTools`"]


YmAction[a_,m_,n_,\[CapitalPsi]_]:=Module[{},
Sqrt[n]ArrayReshape[\[CapitalPsi],{m,m^(n-1)}][[a,All]]//Simplify
];
XmAction[a_,m_,n_,\[CapitalPsi]_]:=Module[{},
Sqrt[n]ArrayReshape[\[CapitalPsi],{m^(n-1),m}][[All,a]]//Simplify
];
InnerProd[\[CapitalPhi]_,\[CapitalPsi]_]:=Conjugate[\[CapitalPhi]].\[CapitalPsi];
YpAction[a_,R_,m_,n_,\[CapitalPsi]_]:=Module[{\[CapitalPsi]c,\[CapitalPsi]s,k},
\[CapitalPsi]c=Flatten@KP[UnitVector[m,a],\[CapitalPsi]];
\[CapitalPsi]s=\[CapitalPsi]c;
k=1;
While[k<=n,
(*Print[\[CapitalPsi]c//Dimensions];
Print[Dimensions@KP[Id[m^(k-1),SparseArray],R,Id[m^(n-k),SparseArray]]];*)
\[CapitalPsi]c=KP[Id[m^(k-1),SparseArray],R,Id[m^(n-k),SparseArray]].\[CapitalPsi]c;
\[CapitalPsi]s+=\[CapitalPsi]c; 
k++;
];
1/Sqrt[n+1] \[CapitalPsi]s//Simplify
];
XpAction[a_,R_,m_,n_,\[CapitalPsi]_]:=Module[{\[CapitalPsi]c,\[CapitalPsi]s,k},
\[CapitalPsi]c=Flatten@KP[\[CapitalPsi],UnitVector[m,a]];
\[CapitalPsi]s=\[CapitalPsi]c;
k=1;
While[k<=n,
\[CapitalPsi]c=KP[Id[m^(n-k),SparseArray],R,Id[m^(k-1),SparseArray]].\[CapitalPsi]c;
\[CapitalPsi]s+=\[CapitalPsi]c; 
k++;
];
1/Sqrt[n+1] \[CapitalPsi]s//Simplify
];
ActionToMatrix[op_,V1_,V2_]:=Table[Simplify@Conjugate[v1].op[v2],{v1,V1},{v2,V2}];
BlockDiag[blocks_]:=Fold[ArrayFlatten[{{#,0},{0,#2}}]&,blocks[[1]],blocks[[2;;-1]]];
UpperBlockDiag[blocks_]:=Module[{d0=Dimensions[blocks[[1]]][[1]],dn=Dimensions[blocks[[-1]]][[2]]},{{0,BlockDiag[blocks]},{ConstantArray[0,{dn,d0}],0}}//ArrayFlatten];
LowerBlockDiag[blocks_]:=Module[{d0=Dimensions[blocks[[1]]][[2]],dn=Dimensions[blocks[[-1]]][[1]]},{{0,ConstantArray[0,{d0,dn}]},{BlockDiag[blocks],0}}//ArrayFlatten];
ParaSpinOperators[R_,nmax_]:=Module[{WfSpaces,m=Sqrt[Length[R]],Yp,Ym,Xp,Xm,Sp,Sm},
WfSpaces=Table[SymSpace[R,n],{n,0,nmax}];
(*Print[1];*)
Yp=Table[LowerBlockDiag@Table[ActionToMatrix[YpAction[a,R,m,n,#]&,WfSpaces[[n+2]],WfSpaces[[n+1]]],{n,0,nmax-1}],{a,1,m}];
(*Print[2];*)
Xp=Table[LowerBlockDiag@Table[ActionToMatrix[XpAction[a,R,m,n,#]&,WfSpaces[[n+2]],WfSpaces[[n+1]]],{n,0,nmax-1}],{a,1,m}];
(*Print[3];*)
Ym=Table[UpperBlockDiag@Table[ActionToMatrix[YmAction[a,m,n+1,#]&,WfSpaces[[n+1]],WfSpaces[[n+2]]],{n,0,nmax-1}],{a,1,m}];
(*Print[4];*)
Xm=Table[UpperBlockDiag@Table[ActionToMatrix[XmAction[a,m,n+1,#]&,WfSpaces[[n+1]],WfSpaces[[n+2]]],{n,0,nmax-1}],{a,1,m}];
Sp=Table[cm[Xm[[b]],Yp[[a]]],{a,1,m},{b,1,m}];
Sm=Table[cm[Ym[[a]],Xp[[b]]],{a,1,m},{b,1,m}];
{Yp,Ym,Xp,Xm,Sp,Sm}
];
(*ST[Yp_,Ym_,Xp_,Xm_]:=Module[{m,d,S,T},
{m,d,d}=Dimensions[Yp];
S=Table[cm[Xm[[b]],Yp[[a]]],{a,1,m},{b,1,m}];
T=Table[cm[Ym[[a]],Xp[[b]]],{a,1,m},{b,1,m}];
{S,T}
];*)
CheckHerm[Yp_,Ym_,Xp_,Xm_]:=Module[{m=Length@Yp},
And@@Table[Yp[[a]]==ConjugateTranspose[Ym[[a]]]&&Xp[[a]]==ConjugateTranspose[Xm[[a]]],{a,1,m}]
];
CheckCommu[Yp_,Xp_]:=Module[{m=Length@Yp},
And@@Flatten@Table[Norm[cm[Yp[[a]],Xp[[b]]]]==0,{a,1,m},{b,1,m}]
];

CheckYAlg[R_,Yp_,Ym_]:=Module[{m,d,R90,R180,YpYp,YmYm,YmYp,YpYm,IdId},
{m,d,d}=Dimensions[Yp];
{R90,R180}=RotatedRmat[R];
YpYp=ContractY[Yp,Yp];
YpYm=ContractY[Yp,Ym];
YmYp=ContractY[Ym,Yp];
YmYm=ContractY[Ym,Ym];
IdId=ArrayReshape[Transpose[ArrayReshape[Id[d m],{d,m,d,m}],2<->3],{d,d,m^2}];
(*Print@Dimensions@YpYp;*)
And[YpYp==YpYp.R,YmYm==YmYm.R180,YmYp==YpYm.R90+IdId]
];
CheckXYAlg[R_,Yp_,Ym_,Xp_,Xm_]:=Module[{m=Length[Yp]},Simplify@And[CheckYAlg[\[CapitalPi][m].R.\[CapitalPi][m],Xp,Xm],CheckYAlg[R,Yp,Ym],CheckCommu[Yp,Xp],CheckCommu[Ym,Xm]]];
cm[x_,y_]:=x.y-y.x;
LA[P_,Yp_,Ym_,Xp_,Xm_]:=Module[{m,d,E12,E21,n},
{m,d,d}=Dimensions[Yp];
E12=Sum[KP[Xp[[i]],Ym[[j]]]*P[[i,j]],{i,1,m},{j,1,m}];
E21=Sum[KP[Xm[[i]],Yp[[j]]]*P[[i,j]],{i,1,m},{j,1,m}];
n=Sum[Yp[[i]].Ym[[j]]*P[[i,j]],{i,1,m},{j,1,m}];
{E12,E21,n}
]

  End[]

  EndPackage[]
