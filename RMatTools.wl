(* ::Package:: *)

BeginPackage[ "RMatTools`"]
  SymSpace::usage = "SymSpace[R,n] computes the space of common eigenstates of \!\(\*SubscriptBox[\(R\), \(12\)]\),\!\(\*SubscriptBox[\(R\), \(23\)]\),...,\!\(\*SubscriptBox[\(R\), \(n - 1, n\)]\) with eigenvalue +1."
  SymSpaceDim::usage = "SymSpaceDim[R,n] computes the dimension of the space of common eigenstates of \!\(\*SubscriptBox[\(R\), \(12\)]\),\!\(\*SubscriptBox[\(R\), \(23\)]\),...,\!\(\*SubscriptBox[\(R\), \(n - 1, n\)]\) with eigenvalue +1. "
  ExclusionStatistics::usage = "ExclusionStatistics[R,ncutoff] computes the exclusion statistics {\!\(\*SubscriptBox[\(d\), \(n\)]\) | 0\[LessEqual]n\[LessEqual]ncutoff } of an R-matrix."
  PartitionFunction::usage = "PartitionFunction[R,ncutoff,x] computes the single mode partition function \!\(\*SubscriptBox[\(z\), \(R\)]\)(x) of an R-matrix."
  RotatedRmat::usage = "RotatedRmat[R] returns the rotated R-matrices {R90,R180} needed for parastatistics."
  RToTensor::usage = "RToTensor[R] gives the 4-index tensor form of R."
  CheckYBE::usage = "CheckYBE[R] checks that R is involutive, and satisfies YBE R12.R23.R12\[Equal]R23.R12.R23."
  CheckSetthYBE::usage = "CheckSetthYBE[r,m] checks that the set-theoretical r-matrix is involutive, and satisfies YBE r12 r23 r12\[Equal]r23 r12 r23."
  SetthToMat::usage = "SetthToMat[r,m] converts seth-theoretical r to an R-matrix."
  SetthPrint::usage=" SetthPrint[r,m] prints the set-theoretical r-matrix."
  
  Begin[ "Private`"]
   SetDirectory[NotebookDirectory[]];
	Needs["TensorTool`"];
    SymSpaceDim[R_,n_]:=Module[{d=Sqrt[Length[R]]},d^n-MatrixRank[H[R-Id[d^2,SparseArray],n]]];
    ExclusionStatistics[R_,ncutoff_]:=Module[{m=Sqrt[Length[R]]},Join[{1,m},Table[SymSpaceDim[R,n],{n,2,ncutoff}]]];
    PartitionFunction[R_,ncutoff_,x_]:=x^Range[0, ncutoff].ExclusionStatistics[R,ncutoff];
	SymSpace[R_,n_]:=SymSpace[R,n]=Module[{d=Sqrt[Length[R]]},
	If[n==0,Return[SparseArray@{{1}}];];
	If[n==1,Return[Id[d,SparseArray]];];
	Simplify@SparseArray@Orthogonalize@NullSpace@H[R-Id[d^2,SparseArray],n]];
	RotatedRmat[R_]:=Module[{m=Sqrt[Length[R]],R90,R180},
	R90=ArrayReshape[Transpose[ArrayReshape[R,{m,m,m,m}],{3,1,4,2}],{m^2,m^2}];
	R180=ArrayReshape[Transpose[ArrayReshape[R,{m,m,m,m}],{4,3,2,1}],{m^2,m^2}];
	{R90,R180}
	];
	RToTensor[R_]:=Module[{d=Sqrt[Dimensions[R][[1]]]},ArrayReshape[R,{d,d,d,d}]];
	CheckSetthYBE[r_,m_]:=Module[{r12,r23},
	r12[l_]:=Module[{x,y,z},{x,y,z}=l;Flatten@{r[[x,y]],z}];
	r23[l_]:=Module[{x,y,z},{x,y,z}=l;Flatten@{x,r[[y,z]]}];
	And@@Flatten@Table[(r12@r12@{x,y,z}=={x,y,z})&&(r12@r23@r12@{x,y,z}==r23@r12@r23@{x,y,z}),{x,1,m},{y,1,m},{z,1,m}]
	];
	SetthPrint[r_,m_]:=Module[{},Table[StringJoin@@ToString/@r[[i,j]],{i,1,m},{j,1,m}]];
	SetthToMat[r_,m_]:=ArrayReshape[SparseArray[Flatten[Table[Join[r[[ii,jj]],{ii,jj}]->1 ,{ii,1,m},{jj,1,m}],1],{m,m,m,m}],{m^2,m^2}];
	CheckYBE[R_]:=Module[{d=Sqrt[Dimensions[R][[1]]],R12,R23},
	R12=KP[R,Id[d]];R23=KP[Id[d],R];
	R12.R23.R12==R23.R12.R23//Simplify
	];
  End[]

  EndPackage[]

