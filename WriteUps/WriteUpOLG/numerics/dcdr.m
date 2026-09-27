% The rate response of consumption itself: max and min of dc/dr over the reach at each age (gamma = 3, r = 4.5%),
% to read the cell enclosure widths of enclmesh.py against the true spread across a cell, and the term
% -(r2 - r1)(a - dc/dr) that the pairwise failure bound gains from a gap between cells.
function dcdr
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; [Pi,y,nu]=tauchen(rho,sigma,nz);
na=600; ag=[0; exp(linspace(log(1e-3),log(300),na-1))'];
for gam=[3 5]
  r=0.045; R=1+r; dlt=1e-4;
  cm=egm(R-dlt,beta,gam,y,Pi,ag,J); cp=egm(R+dlt,beta,gam,y,Pi,ag,J); c=egm(R,beta,gam,y,Pi,ag,J);
  reach=zeros(J,1); a=0;
  for j=1:J-1, k=J-j; v=zeros(1,nz); for z=1:nz, v(z)=interp1(ag,c{k+1}(:,z),a,'linear','extrap'); end; a=max(max(y'+R*a-v),0); reach(j+1)=a; end
  fprintf('gamma %g, r = %.3f:  age | reach | max dc/dr | min dc/dr | max (dc/dr - a) | min (a - dc/dr) on a<=reach   (a<=10 in brackets)\n',gam);
  for j=[1 2 5 10 20 30 40 50 59 60]
    k=J-j; d=(cp{k+1}-cm{k+1})/(2*dlt); ia=ag<=max(reach(j),0.5); i10=ag<=10;
    dd=d(ia,:); aa=repmat(ag(ia),1,nz); d10=d(i10,:); a10=repmat(ag(i10),1,nz);
    fprintf('  %2d | %6.2f | %+8.2f | %+8.2f | %+8.3f | %+8.3f   [%+7.2f %+7.2f]\n',j,reach(j),max(dd(:)),min(dd(:)),max(dd(:)-aa(:)),min(aa(:)-dd(:)),max(d10(:)),min(d10(:)));
  end
end
end
function c=egm(R,beta,gamma,y,Pi,ag,J)
nz=numel(y); na=numel(ag); m=y'+R*ag; c=cell(J,1); c{1}=m;
for k=1:J-1
  up=c{k}.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z);
  end
  c{k+1}=min(cn,m);
end
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
