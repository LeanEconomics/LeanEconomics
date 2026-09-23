% The value-gap condition: is  V_k(a,z;R2) - V_k(a,z;R1)  increasing in a, with slope >= theta > 0?
% Slope of the gap is R2 u'(c2) - R1 u'(c1) by the envelope theorem, so report its minimum.
function valuegap
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; D=0.01;
[Pi,y]=tauchen(rho,sigma,nz);
fprintf(' gam |   r1   | min gap slope (envelope) | min gap increment | increments < 0\n');
for gam=[1 2 3]
  for r1=[0.00 0.04 0.06 0.10]
    [ms,mi,nb]=check(r1,D,beta,gam,y,Pi,J);
    fprintf(' %3.1f | %+.3f | %24.6e | %17.3e | %14d\n',gam,r1,ms,mi,nb);
  end
end
end
function [minslope,minincr,nbad]=check(r1,D,beta,gam,y,Pi,J)
R1=1+r1; R2=1+r1+D; nz=numel(y); na=400;
ag=[0; exp(linspace(log(1e-3),log(300),na-1))'];
[c1,V1]=solve(R1,beta,gam,y,Pi,ag,J); [c2,V2]=solve(R2,beta,gam,y,Pi,ag,J);
minslope=inf; minincr=inf; nbad=0;
for k=1:J                       % stageValue k uses index k+1? here V{k} = value with k periods left
  s=R2*c2{k}.^(-gam)-R1*c1{k}.^(-gam);     % envelope slope of the gap
  minslope=min(minslope,min(s(:)));
  G=V2{k}-V1{k}; dG=diff(G,1,1);           % increments in a
  minincr=min(minincr,min(dG(:))); nbad=nbad+sum(dG(:)<0);
end
end
function [c,V]=solve(R,beta,gamma,y,Pi,ag,J)
nz=numel(y); na=numel(ag); m=y'+R*ag; c=cell(J,1); V=cell(J,1);
c{1}=m; V{1}=util(m,gamma);
for k=1:J-1
  up=c{k}.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z);
  end
  cn=min(cn,m); c{k+1}=cn;
  ap=m-cn; EV=V{k}*Pi'; Vn=zeros(na,nz);
  for z=1:nz
    Vn(:,z)=util(cn(:,z),gamma)+beta*interp1(ag,EV(:,z),min(max(ap(:,z),ag(1)),ag(end)),'linear','extrap');
  end
  V{k+1}=Vn;
end
end
function u=util(c,g), if g==1, u=log(c); else u=c.^(1-g)/(1-g); end, end
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
