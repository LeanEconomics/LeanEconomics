% Can any available bound see the risk correction?
% The correction is a difference of RATE RESPONSES between the risky and CE problems.
% Compare, at zero wealth in the top state: (a) the rate response of consumption per unit dr,
% (b) the width of the sharpest available sandwich on consumption there.
function scale
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; K=J-1; gam=3;
[Pi,y,~]=tauchen(rho,sigma,nz);
na=800; ag=[0; exp(linspace(log(1e-3),log(300),na-1))'];
fprintf('   r    | c(0,zmax) | d c/dr  | sandwich low | sandwich high | width | width/(dc/dr)\n');
for r=[0.02 0.04 0.06]
  R=1+r; c1=egm(R,beta,gam,y,Pi,ag,J); c2=egm(R+1e-4,beta,gam,y,Pi,ag,J);
  c=c1{J}(1,nz); dc=(c2{J}(1,nz)-c1{J}(1,nz))/1e-4;
  Th=(beta*R)^(1/gam); kap=zeros(J,1); kap(1)=1;
  for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
  H=zeros(nz,J); for k=1:K, H(:,k+1)=(Pi*(y+H(:,k)))/R; end
  Hr=zeros(nz,J);
  for k=1:K
    M=zeros(nz,1);
    for z=1:nz, M(z)=(sum(Pi(z,:)'.*(y+Hr(:,k)).^(-gam)))^(-1/gam); end
    Hr(:,k+1)=min(M/R,(1/kap(k+1)-1)*y);
  end
  lo=kap(J)*(y(nz)+Hr(nz,J)); hi=kap(J)*(y(nz)+H(nz,J));
  fprintf(' %+.3f | %9.4f | %+7.4f | %12.4f | %13.4f | %5.3f | %12.1f\n', ...
    r,c,dc,lo,hi,hi-lo,(hi-lo)/abs(dc));
end
fprintf('\n  the correction to be bounded is a DIFFERENCE of such responses between two problems,\n');
fprintf('  so a bound must resolve much less than dc/dr itself.\n');
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
function c=egm(R,beta,gamma,y,Pi,ag,J)
nz=numel(y); na=numel(ag); m=y'+R*ag; c=cell(J,1); c{1}=m;
for k=1:J-1
  up=c{k}.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z);
  end
  cn=min(cn,m); c{k+1}=cn;
end
end
