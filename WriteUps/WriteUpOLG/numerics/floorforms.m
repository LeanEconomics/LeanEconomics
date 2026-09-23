% Which provable floor survives a form Lean can carry?
%  (a) z-dependent affine lower bound on cohortAssets, NO clamp:
%      G_0=1, F_0=0;  G_{k+1} = 1 + G_k (1-kap_{k+1}) R
%                     F_{k+1}(z) = (Pi F_k)(z) + G_k [ (1-kap_{k+1}) y_z - kap_{k+1} H_{k+1}(z) ]
%      floor on capital = nu' F_K / (K+1)
%  (b) uniform y_min / H_max with a clamp at zero on the asset level (as in olgexist.m)
function floorforms
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; gam=3; alpha=9/25; delta=2/25;
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); nu=abs(V(:,k)); nu=nu/sum(nu);
y=exp(xg)'; y=y/(nu'*y);
fprintf('ymin=%.4f  ymean=%.4f  ymax=%.4f\n\n',min(y),nu'*y,max(y));
fprintf('   r     | demand | floor (a) affine | floor (b) uniform+clamp | (a)>dem | (b)>dem\n');
for r=[0.04 0.06 0.08 0.10 0.15 0.20 0.30]
  R=1+r; dem=alpha/((1-alpha)*(r+delta)); K=J-1;
  Th=(beta*R)^(1/gam);
  kap=zeros(J,1); kap(1)=1; for k=1:J-1, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
  H=zeros(nz,J); for k=1:J-1, H(:,k+1)=(Pi*(y+H(:,k)))/R; end
  % (a)
  G=1; F=zeros(nz,1);
  for k=0:K-1
    Fn=Pi*F + G*((1-kap(k+2))*y - kap(k+2)*H(:,k+2));
    G=1+G*(1-kap(k+2))*R; F=Fn;
  end
  fa=(nu'*F)/J;
  % (b)
  ymin=min(y); B=0; tot=0;
  for j=0:J-1
    tot=tot+B; kk=J-1-j; if j==J-1, break; end
    B=max(0,(1-kap(kk+1))*(ymin+R*B)-kap(kk+1)*max(H(:,kk+1)));
  end
  fb=tot/J;
  fprintf(' %+.4f | %6.3f | %16.4f | %23.4f | %7s | %7s\n',r,dem,fa,fb, ...
     string(fa>dem),string(fb>dem));
end
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
