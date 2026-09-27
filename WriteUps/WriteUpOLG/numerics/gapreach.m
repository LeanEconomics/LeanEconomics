% Where does the value gap (B): R1*c_k(a;R2) <= R2*c_k(a;R1) fail, and is it inside the
% region a cohort can reach?  reach(j) = assets after j periods of the max-earnings path at R2.
function gapreach
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
[Pi,y]=tauchen(rho,sigma,nz);
r1=0.04; D=0.02; R1=1+r1; R2=1+r1+D; na=600;
ag=[0; exp(linspace(log(1e-3),log(300),na-1))'];
for gam=[1.5 2 3]
  c1=egm(R1,beta,gam,y,Pi,ag,J); c2=egm(R2,beta,gam,y,Pi,ag,J);
  % reach along the max-income path at R2: age j has k=J-j periods to go
  reach=zeros(J,1); a=0;
  for j=1:J-1
    k=J-j; g=y(end)+R2*a-interp1(ag,c2{k+1}(:,end),a,'linear','extrap'); a=max(g,0); reach(j+1)=a;
  end
  fprintf('gamma=%.1f  max reach %.2f\n',gam,max(reach));
  fprintf('  k | first-failing asset (any z) | reach at that age | fails inside reach?\n');
  worst=0;
  for k=[1 2 3 5 10 20 30 40 50 59]
    A=c1{k+1}; B=c2{k+1}; bad=any(R1*B>R2*A*(1+1e-12),2);
    i=find(bad,1); af=inf; if ~isempty(i), af=ag(i); end
    rj=reach(J-k+1);  % cohort with k periods to go is age J-k -> index J-k+1
    fprintf(' %2d | %10.3f | %8.3f | %s\n',k,af,rj,string(af<=rj));
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
function [Pi,y]=tauchen(rho,sigma,nz)
sd=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd; hi=(xg(j)+h/2-rho*xg(i))/sd;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,Dg]=eig(Pi'); [~,k]=max(abs(diag(Dg))); nu=abs(V(:,k)); nu=nu/sum(nu);
y=exp(xg)'; y=y/(nu'*y);
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
