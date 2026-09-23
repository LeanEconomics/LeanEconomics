% (B) "the marginal value of assets rises with the rate":  R1*c_k(a,z;R2) <= R2*c_k(a,z;R1).
% (A) Light's Theorem 1:  g_k(a,z;R1) <= g_k(a,z;R2).
% Check both on the whole grid, all ages, several gamma and r.
function condB
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
[Pi,y]=tauchen(rho,sigma,nz);
fprintf(' gam |   r1   |   D    | min (B) margin | (B) bad%% | min (A) margin | (A) bad%%\n');
for gam=[1 2 3 3.5 5]
  for r1=[0.00 0.04 0.06 0.10]
    D=0.01;
    [mb,fb,ma,fa]=check(r1,D,beta,gam,y,Pi,J);
    fprintf(' %3.1f | %+.3f | %.4f | %+14.3e | %7.2f | %+14.3e | %7.2f\n',gam,r1,D,mb,100*fb,ma,100*fa);
  end
end
end
function [mb,fb,ma,fa]=check(r1,D,beta,gam,y,Pi,J)
R1=1+r1; R2=1+r1+D; nz=numel(y); na=400;
ag=[0; exp(linspace(log(1e-3),log(300),na-1))'];
c1=egm(R1,beta,gam,y,Pi,ag,J); c2=egm(R2,beta,gam,y,Pi,ag,J);
m1=y'+R1*ag; m2=y'+R2*ag;
mb=inf; nb=0; ma=inf; nastate=0; ntot=0;
for k=0:J-1
  A=c1{k+1}; B=c2{k+1};
  % (B): R1*B <= R2*A
  mrg=(R2*A-R1*B)./abs(R2*A); mb=min(mb,min(mrg(:))); nb=nb+sum(mrg(:)<0);
  % (A): g1 <= g2  with g = m - c
  g1=m1-A; g2=m2-B; sc=max(abs(g1),1e-8);
  mrgA=(g2-g1)./sc; ma=min(ma,min(mrgA(:))); nastate=nastate+sum(mrgA(:)<-1e-10);
  ntot=ntot+numel(A);
end
fb=nb/ntot; fa=nastate/ntot;
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
