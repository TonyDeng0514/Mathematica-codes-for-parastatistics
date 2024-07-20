(* ::Package:: *)

BeginPackage[ "TensorTool`"]

  el::usage = 
	"el[i,j,n] gives the n*n matrix with (i,j) element equal to 1";
  KP::usage ="=KroneckerProduct";
  Id::usage ="=IdentityMatrix";
  SVD::usage ="=SingularValueDecomposition.";
  \[Delta]::usage ="=KroneckerDelta";
  H::usage ="H[h,n] construct the n-site Hamiltonian from the local Hamiltonian h.";
  \[CapitalPi]::usage = "\[CapitalPi][n] gives the n*n swap matrix";
  ContractY::usage = "ContractY[Y1,Y2] vertically contract the two Y-triangles Y1,Y2.";
  partialTr::usage= "For a d1 d2 * d1 d2 matrix M, partialTr[M,d1,d2] take the partial trace in the first tensor factor space, and obtain a d2*d2 matrix."
  Begin[ "Private`"]
	el[i_,j_,n_]:=el[i,j,n]=Module[{M=ConstantArray[0,{n,n},SparseArray]},M[[i,j]]=1;M];
	KP=KroneckerProduct;
	Id=IdentityMatrix;
	SVD=SingularValueDecomposition;
	\[Delta]=KroneckerDelta;
	H[h_,n_]:=Module[{d=Sqrt[Length[h]]},If[n==2, h,KP[H[h,n-1],Id[d,SparseArray]]+KP[Id[d^(n-2),SparseArray], h]]];
	\[CapitalPi][n_]:=\[CapitalPi][n]=Sum[KP[el[i,j,n],el[j,i,n]],{i,1,n},{j,1,n}];
	ContractY[Y1_,Y2_]:=Module[{m,d},
		{m,d,d}=Dimensions[Y1];
		Transpose[ArrayReshape[Transpose[Y1,1<->2].Transpose[Y2,1<->2],{d,m^2,d}],2<-> 3]
	];
    partialTr[M_,d1_,d2_]:=Flatten[Id[d1]].ArrayReshape[Transpose[ArrayReshape[M,{d1,d2,d1,d2}],2<-> 3],{d1^2,d2,d2}];
  End[]

  EndPackage[]

