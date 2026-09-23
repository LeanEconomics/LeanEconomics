% The sharper ceiling: smallest B with  max_{j,w} (1-kap_j)(y_w + R B) - kap_j H_j(w) <= B.
% Compare with feasibility: smallest B with  R B + ymax <= B.
function ceiling
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; gam=3; alpha=9/25; delta=2/25;
[Pi,y]=tauchen(rho,sigma,nz);
fprintf('   r    | demand  | feasibility B | incidence B | sharper r_lo allowed\n');
for r=[-0.07 -0.06 -0.055 -0.05 -0.04]
  R=1+r; Th=(beta*R)^(1/gam); K=J-1; dem=alpha/((1-alpha)*(r+delta));
  kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
  H=zeros(nz,J);
  for k=1:K
    M=zeros(nz,1);
    for z=1:nz, M(z)=(sum(Pi(z,:)'.*(y+H(:,k)).^(-gam)))^(-1/gam); end
    H(:,k+1)=min(M/R,(1/kap(k+1)-1)*y);
  end
  if R<1, Bf=max(y)/(1-R); else Bf=inf; end
  % iterate B <- max_{j,w} (1-kap_j)(y_w + R B) - kap_j H_j(w), clamped below at 0
  B=0;
  for it=1:100000
    best=0;
    for j=1:J
      v=(1-kap(j))*(y+R*B)-kap(j)*H(:,j);
      best=max(best,max(v));
    end
    if abs(best-B)<1e-12, B=best; break; end
    if best>1e8, B=inf; break; end
    B=best;
  end
  fprintf(' %+.3f | %7.3f | %13.2f | %11.2f | %s\n',r,dem,Bf,B,string(B<dem));
end
% smallest r_lo for which the incidence ceiling is below demand
fprintf('\n bisect r_lo: feasibility vs incidence\n');
for mode=1:2
  lo=-0.0799; hi=-0.01;
  for it=1:80
    m=(lo+hi)/2; if ok(m,mode,beta,gam,J,y,Pi,alpha,delta), lo=m; else hi=m; end
  end
  names={'feasibility','incidence'};
  fprintf('   %-12s : r_lo can be as high as %+.4f\n',names{mode},lo);
end
end
function t=ok(r,mode,beta,gam,J,y,Pi,alpha,delta)
R=1+r; Th=(beta*R)^(1/gam); K=J-1; nz=numel(y); dem=alpha/((1-alpha)*(r+delta));
if R>=1, t=false; return; end
if mode==1, t=(max(y)/(1-R))<dem; return; end
kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
H=zeros(nz,J);
for k=1:K
  M=zeros(nz,1);
  for z=1:nz, M(z)=(sum(Pi(z,:)'.*(y+H(:,k)).^(-gam)))^(-1/gam); end
  H(:,k+1)=min(M/R,(1/kap(k+1)-1)*y);
end
B=0;
for it=1:200000
  best=0;
  for j=1:J, v=(1-kap(j))*(y+R*B)-kap(j)*H(:,j); best=max(best,max(v)); end
  if abs(best-B)<1e-12, B=best; break; end
  if best>1e8, B=inf; break; end
  B=best;
end
t=(B<dem);
end
function [Pi,y,nu]=tauchen(rho,sigma,nz)
sd=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd; hi=(xg(j)+h/2-rho*xg(i))/sd;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,Dg]=eig(Pi'); [~,k]=max(abs(diag(Dg))); nu=abs(V(:,k)); nu=nu/sum(nu);
y=exp(xg)'; y=y/(nu'*y);
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
