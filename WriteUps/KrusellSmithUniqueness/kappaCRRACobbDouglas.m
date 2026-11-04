% Contraction modulus kappa of KrusellSmith/CRRAContraction.lean (crraContractionHyp), evaluated
% at Krusell-Smith style calibrations. Every constant follows the Lean definitions exactly:
%   returnBound, wageBound, wageLo            (CobbDouglas.lean)
%   incomeFloor, maxCash, topCons, valueBound, slopeConst   (Inada.lean)
%   crraRadius, crraFloorLevel, Mdu, m, cdLip (CRRAContraction.lean)
%   D, q, A, kappa                            (Contraction.lean)
% kappa < 1 gives existence and uniqueness of sequential equilibrium and the recursive equilibrium.

diary('kappaCRRACobbDouglas.txt'); diary on

% Annual calibration
Par.beta=0.96; Par.alpha=0.36; Par.delta=0.1;
Par.zLo=0.99; Par.zHi=1.01;
Par.eff=[0.25, 1];          % idiosyncratic efficiencies; labour clamp [effLo, effHi]
Par.gamma=2;

% The weighted norm needs beta*Rbar < lambda <= 1 and lambda*Rbar < 1, so beta*Rbar^2 < 1:
% the highest gross return (at capLo, labHi) must be below beta^(-1/2). This puts capLo above
% the complete-markets steady state.
Kcm=(Par.alpha*1/(1/Par.beta-1+Par.delta))^(1/(1-Par.alpha)); % complete markets, L=1
capLoMin=capLoBound(Par);
fprintf('Complete-markets capital (L=1): %8.4f\n',Kcm)
fprintf('Smallest capLo with beta*Rbar^2 < 1: %8.4f\n',capLoMin)

fprintf('\nBaseline: capLo = 1.05*bound, capHi = 2*capLo, assetCap = 3*capHi\n')
fprintf('%6s %12s %12s %12s %12s %12s %12s %12s\n','gamma','cLo','D','Mdu','m','ell','kappa','ell*')
for gamma=[1,2,5]
    Par.gamma=gamma;
    Par.capLo=1.05*capLoBound(Par); Par.capHi=2*Par.capLo; Par.assetCap=3*Par.capHi;
    out=kappaOf(Par);
    fprintf('%6.2f %12.4e %12.4e %12.4e %12.4e %12.4e %12.4e %12.4e\n',gamma,out.cLo,out.D,out.Mdu,out.m,out.ell,out.kappa,out.ell/out.kappa)
end

% kappa is proportional to ell for fixed other constants; ell* = ell/kappa is the price
% Lipschitz constant the theorem would need. Sweep the capital share alpha (prices flatten as
% alpha -> 0) to find where kappa crosses one.
fprintf('\nCapital-share sweep, gamma=2, capital box and asset cap fixed at the alpha=0.36 baseline\n')
fprintf('%10s %12s %12s %12s %12s\n','alpha','Rbar','ell','kappa','cLo')
Par.gamma=2; Par.alpha=0.36;
Par.capLo=1.05*capLoBound(Par); Par.capHi=2*Par.capLo; Par.assetCap=3*Par.capHi;
alphavec=[0.36,0.1,1e-2,1e-4,1e-8,1e-12,1e-16,1e-18,1e-20];
for alpha=alphavec
    Par.alpha=alpha;
    out=kappaOf(Par);
    fprintf('%10.2e %12.6f %12.4e %12.4e %12.4e\n',alpha,out.Rbar,out.ell,out.kappa,out.cLo)
end

diary off

function capLo=capLoBound(Par)
% smallest capLo with beta*Rbar^2 < 1, where Rbar = 1-delta+alpha*zHi*capLo^(alpha-1)*labHi^(1-alpha)
labHi=max(Par.eff);
Rmax=Par.beta^(-1/2);
capLo=((Rmax-1+Par.delta)/(Par.alpha*Par.zHi*labHi^(1-Par.alpha)))^(1/(Par.alpha-1));
end

function out=kappaOf(Par)
a=Par.alpha; g=Par.gamma; b=Par.beta;
labLo=min(Par.eff); labHi=max(Par.eff); effLo=min(Par.eff);
Rbar=1-Par.delta+a*Par.zHi*Par.capLo^(a-1)*labHi^(1-a);
wageBound=(1-a)*Par.zHi*Par.capHi^a*labLo^(-a);
wageLo=(1-a)*Par.zLo*Par.capLo^a*labHi^(-a);
incomeFloor=wageLo*effLo;
maxCash=Rbar*Par.assetCap+wageBound*sum(Par.eff);
topCons=max(incomeFloor,maxCash);
if g==1
    u=@(c) log(c);
else
    u=@(c) c.^(1-g)/(1-g);
end
valueBound=max(abs(u(incomeFloor)/(1-b)),abs(u(topCons)/(1-b)));
slopeConst=4*valueBound/incomeFloor;
r=(b*slopeConst+1)^(-1/g);
cLo=min(r,incomeFloor/4);
floor=cLo/2;
D=cLo^(-g);
Mdu=g*floor^(-g-1);
m=g*topCons^(-g-1);
returnLip=a*Par.zHi*labHi^(1-a)*((1-a)*Par.capLo^(a-2));
wageLip=(1-a)*Par.zHi*labLo^(-a)*(a*Par.capLo^(a-1));
ell=max(returnLip,wageLip);
C=Par.assetCap+sum(Par.eff);
% minimise kappa over admissible lambda: beta*Rbar < lambda <= min(1, 1/Rbar)
lamvec=linspace(b*Rbar,min(1,1/Rbar),2002); lamvec=lamvec(2:end-1);
kap=zeros(size(lamvec));
for ii=1:length(lamvec)
    lam=lamvec(ii);
    q=b*Rbar/lam;
    A=(b*ell*D/lam+Mdu*ell*C)/(1-q);
    kap(ii)=lam*(ell*C+A/m)/(1-lam*Rbar);
end
[kappa,ind]=min(kap);
out=struct('Rbar',Rbar,'cLo',cLo,'D',D,'Mdu',Mdu,'m',m,'ell',ell,'kappa',kappa,'lam',lamvec(ind));
end
