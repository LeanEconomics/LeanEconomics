% Is Phi(K, p(Khat)) monotone in Khat at fixed K?  (W) as stated needs it to be DECREASING.
%   Phi(K,plan) = sum_t beta^t E[ u'(c_t) (a_t - K y_t) ],  c_t priced at K, plan's own a.
function mfgW
alpha=9/25; delta=2/25; J=60; rho=0.9; sigma=0.4; nz=7; beta=0.96;
[y,Pi,nu]=shocks(rho,sigma,nz);
na=800; ag=[0; exp(linspace(log(1e-3),log(4000),na-1))'];
fr=[0.50 0.70 0.80 0.90 0.95 0.98 1.00 1.02 1.05 1.10 1.20 1.40 1.70 2.00];
for gam=[1 3 5]
  rst=eqrate(beta,gam,alpha,delta,y,Pi,nu,J,ag); Kst=(alpha/(rst+delta))^(1/(1-alpha));
  n=numel(fr); C=cell(n,1); A=zeros(n,1);
  for i=1:n, C{i}=cand(Kst*fr(i),beta,gam,alpha,delta,y,Pi,nu,J,ag); A(i)=C{i}.A; end
  fprintf('\n=== gamma = %g :  K* = %.4f ===\n',gam,Kst);
  fprintf('  Khat/K*   :'); fprintf(' %7.2f',fr); fprintf('\n');
  fprintf('  A(Khat)   :'); fprintf(' %7.3f',A); fprintf('\n');
  for Kf=[0.90 1.00 1.10]
    K=Kst*Kf; v=zeros(n,1);
    for i=1:n, v(i)=Phi(C{i},gam,ag,J,y,nz,K,alpha,delta,beta); end
    fprintf('  Phi(K=%.2fK*): ',Kf); fprintf(' %7.3f',v); fprintf('\n');
    d=diff(v); nb=sum(d>0);
    fprintf('     increases in Khat on %d of %d steps (need 0 for (W) as a monotone claim)\n',nb,n-1);
    if nb>0
      j=find(d>0); fprintf('     rising between Khat/K* = ');
      fprintf('%.2f-%.2f ',[fr(j);fr(j+1)]); fprintf('\n');
    end
  end
  % all pairs: does Phi(K,plan with larger A) >= Phi(K,other) hold at every common K in [A2,A1]?
  bad=0; tot=0; worst=0;
  for i=1:n, for k=i+1:n
    if A(i)>A(k), P=C{i}; Q=C{k}; else, P=C{k}; Q=C{i}; end
    if abs(P.A-Q.A)<1e-9, continue; end
    for lam=[0 0.25 0.5 0.75 1]
      K=Q.A+lam*(P.A-Q.A); tot=tot+1;
      g=Phi(P,gam,ag,J,y,nz,K,alpha,delta,beta)-Phi(Q,gam,ag,J,y,nz,K,alpha,delta,beta);
      if g<0, bad=bad+1; worst=min(worst,g); end
    end
  end, end
  fprintf('  (W) over all pairs x 5 pricing points: %d of %d FAIL; worst %+.5f\n',bad,tot,worst);
end
end
function v=Phi(X,gam,ag,J,y,nz,K,alpha,delta,beta)
r=alpha*K^(alpha-1)-delta; w=(1-alpha)*K^alpha; v=0;
for j=1:J
  mu=X.mu(:,:,j); ap=X.ap(:,:,j);
  for z=1:nz
    a=X.w*ag; c=w*y(z)+(1+r)*a-X.w*ap(:,z); ok=c>1e-12;
    v=v+beta^(j-1)*sum(mu(ok,z).*(c(ok).^(-gam)).*(a(ok)-K*y(z)));
  end
end
end
function E=cand(Kh,beta,gam,alpha,delta,y,Pi,nu,J,ag)
E.r=alpha*Kh^(alpha-1)-delta; E.w=(1-alpha)*Kh^alpha; E.Kh=Kh;
[S,E.mu,E.ap]=supply(1+E.r,beta,gam,y,Pi,nu,J,ag); E.A=E.w*S;
end
function r=eqrate(beta,gam,alpha,delta,y,Pi,nu,J,ag)
f=@(rr) supply(1+rr,beta,gam,y,Pi,nu,J,ag)-alpha/((1-alpha)*(rr+delta));
lo=-0.02; hi=0.60; flo=f(lo);
for it=1:40, mid=0.5*(lo+hi); fm=f(mid); if flo*fm<=0, hi=mid; else, lo=mid; flo=fm; end, end
r=0.5*(lo+hi);
end
function [S,MU,AP]=supply(R,beta,gam,y,Pi,nu,J,ag)
nz=numel(y); na=numel(ag); c=egm(R,beta,gam,y,Pi,ag,J); m=y'+R*ag;
MU=zeros(na,nz,J); AP=zeros(na,nz,J); mu=zeros(na,nz); mu(1,:)=nu'; tot=0;
for j=0:J-1
  k=J-1-j; ap=max(m-c{k+1},0); MU(:,:,j+1)=mu; AP(:,:,j+1)=ap; tot=tot+sum(mu,2)'*ag;
  if j==J-1, break; end
  new=zeros(na,nz);
  for z=1:nz
    w=mu(:,z); x=min(max(ap(:,z),ag(1)),ag(end));
    bin=discretize(x,ag); bin(isnan(bin))=na-1; bin=max(min(bin,na-1),1);
    frac=(x-ag(bin))./(ag(bin+1)-ag(bin));
    new=new+accumarray([bin;bin+1],[w.*(1-frac);w.*frac],[na 1])*Pi(z,:);
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
  c{k+1}=min(cn,m);
end
end
function [y,Pi,nu]=shocks(rho,sigma,nz)
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1); Pi=zeros(nz);
for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi0(hi); elseif j==nz, Pi(i,j)=1-Phi0(lo); else, Pi(i,j)=Phi0(hi)-Phi0(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); nu=abs(V(:,k)); nu=nu/sum(nu);
y=exp(xg)'; y=y/(nu'*y);
end
function v=Phi0(x), v=0.5*erfc(-x/sqrt(2)); end
