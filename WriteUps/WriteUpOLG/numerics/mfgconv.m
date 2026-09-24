% Does the date-0 failure survive as the two equilibria approach each other?
function mfgconv
alpha=9/25; delta=2/25; J=60; rho=0.9; sigma=0.4; nz=7;
[y,Pi,nu]=shocks(rho,sigma,nz);
na=800; ag=[0; exp(linspace(log(1e-3),log(4000),na-1))'];
for gam=[1 3]
  fprintf('\n=== gamma = %g :  scaled by (dbeta)^2 ===\n',gam);
  fprintf('  dbeta  |    P_0/d^2   |  total/d^2  | lin total/d^2 | #neg dates\n');
  A=solveEq(0.960,gam,alpha,delta,y,Pi,nu,J,ag);
  for d=[0.02 0.01 0.005 0.0025 0.00125]
    B=solveEq(0.960-d,gam,alpha,delta,y,Pi,nu,J,ag);
    neg=0; tot=0; totlin=0; P0=0;
    for j=1:J
      [P,Plin]=pairAge(A,B,gam,ag,j,y,nz);
      tot=tot+P; totlin=totlin+Plin; if P<0, neg=neg+1; end
      if j==1, P0=P; end
    end
    fprintf(' %7.5f | %+12.6f | %+11.6f | %+13.6f | %5d\n',d,P0/d^2,tot/d^2,totlin/d^2,neg);
  end
  % independent date-0 recomputation, straight from the primitives
  B=solveEq(0.955,gam,alpha,delta,y,Pi,nu,J,ag);
  s1=A.w*A.ap(1,:,1); s2=B.w*B.ap(1,:,1);
  d1=sum(nu'.*(uu(A.w*y'-s1,gam)-uu(B.w*y'-s1,gam)));
  d2=sum(nu'.*(uu(A.w*y'-s2,gam)-uu(B.w*y'-s2,gam)));
  fprintf('  date 0 direct: d1=%+.8f d2=%+.8f  P_0=%+.8f   mean saving s1=%.4f s2=%.4f\n',...
          d1,d2,-(d1-d2),nu'*s1',nu'*s2');
end
end
% ---------------------------------------------------------------- equilibrium
function E=solveEq(beta,gam,alpha,delta,y,Pi,nu,J,ag)
% normalised market clearing: S_unit(r) = alpha/((1-alpha)(r+delta))
f=@(r) supply(1+r,beta,gam,y,Pi,nu,J,ag)-alpha/((1-alpha)*(r+delta));
lo=-0.02; hi=0.60;  % OLG: supply is bounded, so the equilibrium need not sit below lambda
flo=f(lo); fhi=f(hi);
if flo*fhi>0, error('no bracket: f(lo)=%g f(hi)=%g',flo,fhi); end
for it=1:40
  mid=0.5*(lo+hi); fm=f(mid);
  if flo*fm<=0, hi=mid; fhi=fm; else, lo=mid; flo=fm; end
end
E.r=0.5*(lo+hi); E.beta=beta; E.R=1+E.r;
E.K=(alpha/(E.r+delta))^(1/(1-alpha));
E.w=(1-alpha)*E.K^alpha;
[E.S,E.mu,E.ap]=supply(E.R,beta,gam,y,Pi,nu,J,ag);
end
% ---------------------------------------------------------- household + dist
function [S,MU,AP]=supply(R,beta,gam,y,Pi,nu,J,ag)
nz=numel(y); na=numel(ag); c=egm(R,beta,gam,y,Pi,ag,J); m=y'+R*ag;
MU=zeros(na,nz,J); AP=zeros(na,nz,J);
mu=zeros(na,nz); mu(1,:)=nu'; tot=0;
for j=0:J-1
  k=J-1-j; ap=m-c{k+1}; ap=max(ap,0);
  MU(:,:,j+1)=mu; AP(:,:,j+1)=ap;
  tot=tot+sum(mu,2)'*ag;
  if j==J-1, break; end
  new=zeros(na,nz);
  for z=1:nz
    w=mu(:,z);
    x=min(max(ap(:,z),ag(1)),ag(end));
    bin=discretize(x,ag); bin(isnan(bin))=na-1; bin=max(min(bin,na-1),1);
    frac=(x-ag(bin))./(ag(bin+1)-ag(bin));
    mass=accumarray([bin;bin+1],[w.*(1-frac);w.*frac],[na 1]);
    new=new+mass*Pi(z,:);
  end
  mu=new;
end
S=tot/J;
end
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
% -------------------------------------------------------------- the pairing
function pairing(A,B,gam,ag,J,y,nz)
neg=0; tot=0; totlin=0; bad=0; worst=1e9; wage=0;
fprintf('   age |    P_t (true u)  |  P_t (u affine)  |   ratio\n');
for j=1:J
  [P,Plin,nb]=pairAge(A,B,gam,ag,j,y,nz);
  bad=bad+nb; tot=tot+P; totlin=totlin+Plin;
  if P<0, neg=neg+1; end
  if P<worst, worst=P; wage=j; end
  if any(j==[1 2 5 10 20 30 40 50 59 60])
    fprintf('  %4d | %+16.9f | %+16.9f | %+8.4f\n',j-1,P,Plin,P/Plin);
  end
end
fprintf('  total| %+16.9f | %+16.9f | %+8.4f\n',tot,totlin,tot/totlin);
fprintf('  dates with P_t < 0: %d of %d;  worst P_t = %+.6e at age %d;  mass with c<=0: %.2e\n',...
        neg,J,worst,wage-1,bad);
end
function [P,Plin,bad]=pairAge(A,B,gam,ag,j,y,nz)
% d_i = int [ u(c(x,K_A)) - u(c(x,K_B)) ] dm_i ;  P = -(d_1 - d_2)
[d1,b1]=core(A,A,B,gam,ag,j,y,nz);
[d2,b2]=core(B,A,B,gam,ag,j,y,nz);
P=-(d1-d2); bad=b1+b2;
% affine-utility counterpart: -(r1-r2)*(A1-A2), with A_i the LEVEL assets at this age
a1=sum(A.mu(:,:,j),2)'*ag*A.w; a2=sum(B.mu(:,:,j),2)'*ag*B.w;
Plin=-(A.r-B.r)*(a1-a2);
end
function [d,bad]=core(X,P1,P2,gam,ag,j,y,nz)
mu=X.mu(:,:,j); ap=X.ap(:,:,j);
d=0; bad=0;
for z=1:nz
  a=X.w*ag; s=X.w*ap(:,z);
  c1=P1.w*y(z)+(1+P1.r)*a-s;
  c2=P2.w*y(z)+(1+P2.r)*a-s;
  ok=(c1>1e-12)&(c2>1e-12);
  bad=bad+sum(mu(~ok,z));
  d=d+sum(mu(ok,z).*(uu(c1(ok),gam)-uu(c2(ok),gam)));
end
end
function v=uu(c,g)
if abs(g-1)<1e-12, v=log(c); else, v=(c.^(1-g)-1)/(1-g); end
end
% ------------------------------------------------------------------- shocks
function [y,Pi,nu]=shocks(rho,sigma,nz)
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz);
for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else, Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); nu=abs(V(:,k)); nu=nu/sum(nu);
y=exp(xg)'; y=y/(nu'*y);
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
