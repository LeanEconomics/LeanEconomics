% Can the mass-weighted failure of Theorem 1 be bounded from primitives?
%   ebar_j = E_1[ (g^1_j - g^2_j)^+ ]  with the expectation under the r1 economy at age j.
%   Route: if the violation vanishes below a threshold A*, then
%       ebar_j <= sup_{a>=A*} v  *  P(a_j >= A*)  <=  sup v * E[a_j]/A*      (Markov)
%   and E[a_j] is bounded above by the affine ceiling already proved for existence.
function ebar
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; alpha=9/25; delta=2/25;
[Pi,y,nu]=tauchen(rho,sigma,nz);
D=@(r) alpha/((1-alpha)*(r+delta));
na=500; ag=[0; exp(linspace(log(1e-3),log(4000),na-1))'];
for pr=[0.04 0.06; 0.02 0.08]'
  r1=pr(1); r2=pr(2); budget=D(r1)-D(r2);
  fprintf('\n######## r1=%.2f r2=%.2f, budget %.4f ########\n',r1,r2,budget);
  for gam=[5 8]
    [~,M1,G1]=run(1+r1,beta,gam,y,Pi,nu,J,ag);
    [~,M2,G2]=run(1+r2,beta,gam,y,Pi,nu,J,ag);
    % where does the violation live?
    amin=inf; vmax=0; Ea=zeros(J,1); eb=zeros(J,1);
    for j=1:J
      for z=1:nz
        v=max(0,G1(:,z,j)-G2(:,z,j));
        hit=find(v>1e-10);
        if ~isempty(hit), amin=min(amin,ag(hit(1))); end
        vmax=max(vmax,max(v));
        eb(j)=eb(j)+sum(M1(:,z,j).*v);
      end
      Ea(j)=sum(M1(:,:,j),2)'*ag;
    end
    fprintf(' gamma=%g : violation first appears at a = %.4f ; sup violation %.5f ; max E[a_j] %.3f\n',...
            gam,amin,vmax,max(Ea));
    % Lipschitz accumulation
    R2=1+r2; Th=(beta*R2)^(1/gam); kap=zeros(J,1); kap(1)=1;
    for k=1:J-1, kap(k+1)=kap(k)*R2/(Th+kap(k)*R2); end
    L=zeros(J,1); for j=1:J, L(j)=(1-kap(J-j+1))*R2; end
    % the income marginal is EXACTLY nu at every age (the chain starts from nu), so
    %    ebar_j <= sum_z nu(z) * sup_a v(a,z,j)
    Bz=zeros(J,1); vz=zeros(nz,1);
    for j=1:J, for z=1:nz
      v=max(0,G1(:,z,j)-G2(:,z,j));
      Bz(j)=Bz(j)+nu(z)*max(v); vz(z)=max(vz(z),max(v));
    end, end
    accz=accumEps(L,Bz,J);
    fprintf('        sup_a violation by income state: '); fprintf('%8.5f',vz); fprintf('\n');
    fprintf('        nu: '); fprintf('%8.5f',nu); fprintf('\n');
    fprintf('        nu-weighted bound: max_j %.6f, accumulated %.6f   %s\n',...
            max(Bz),accz,tick(accz<budget));
    fprintf('        true max ebar_j = %.3e, accumulated %.6f\n',max(eb),accumEps(L,eb,J));
  end
end
end
function B=accumEps(L,ep,J)
e=0; tot=0;
for j=1:J, tot=tot+e; if j<J, e=L(j)*e+ep(j); end, end
B=tot/J;
end
function s=tick(b), if b, s='PASS'; else, s='fail'; end, end
function [S,MU,GP]=run(R,beta,gam,y,Pi,nu,J,ag)
nz=numel(y); na=numel(ag); c=egm(R,beta,gam,y,Pi,ag,J); m=y'+R*ag;
MU=zeros(na,nz,J); GP=zeros(na,nz,J); mu=zeros(na,nz); mu(1,:)=nu'; tot=0;
for j=0:J-1
  k=J-1-j; ap=max(m-c{k+1},0); MU(:,:,j+1)=mu; GP(:,:,j+1)=ap; tot=tot+sum(mu,2)'*ag;
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
