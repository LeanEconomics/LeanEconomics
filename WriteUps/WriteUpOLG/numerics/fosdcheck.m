% Light-Weintraub Thm 2 needs the cohort distributions ORDERED, which its hypothesis delivers via
% the POINTWISE policy ordering.  Does the ordering survive where the policy ordering fails?
%   wage units (w = 1): household faces income y(z), gross return R.  Common asset grid, so the
%   distributions at two rates are directly comparable with no interpolation.
%   (L) policy:  ap(a,z,j; r2) >= ap(a,z,j; r1)  for r2 > r1      [Light's Theorem 1]
%   (F) FOSD:    CDF_j(x; r2) <= CDF_j(x; r1)  at every age and threshold
%   (Fz) the same conditional on each income state -- what operator domination actually needs.
function fosdcheck
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
[Pi,y,nu]=tauchen(rho,sigma,nz);
na=800; ag=[0; exp(linspace(log(1e-3),log(4000),na-1))'];
for pr=[0.04 0.06; 0.02 0.08]'
  fprintf('\n################  r1 = %.2f  vs  r2 = %.2f  ################\n',pr(1),pr(2));
  fprintf(' gam | (L) policy viol.  | (F) marginal FOSD      | (Fz) FOSD given z      | S(r1)  S(r2)\n');
  fprintf('     | mass      worst   | ages bad  worst CDF gap| ages bad  worst gap    |\n');
  for gam=[1 2 3 5 8]
    [S1,M1,A1]=run(1+pr(1),beta,gam,y,Pi,nu,J,ag);
    [S2,M2,A2]=run(1+pr(2),beta,gam,y,Pi,nu,J,ag);
    % (L) policy ordering, weighted by the r1 distribution
    vm=0; vw=0;
    for j=1:J
      d=A1(:,:,j)-A2(:,:,j);                   % >0 means r2 saves LESS: a violation
      bad=d>1e-10;
      vm=vm+sum(M1(:,:,j).*bad,'all'); vw=max(vw,max(d(:)));
    end
    vm=vm/J;
    % (F) marginal FOSD:  CDF2 <= CDF1
    nb=0; wg=0;
    for j=1:J
      c1=cumsum(sum(M1(:,:,j),2)); c2=cumsum(sum(M2(:,:,j),2));
      g=max(c2-c1); if g>1e-10, nb=nb+1; end; wg=max(wg,g);
    end
    % (Fz) conditional on z
    nbz=0; wgz=0;
    for j=1:J
      bad=false;
      for z=1:nz
        m1=M1(:,z,j); m2=M2(:,z,j); s1=sum(m1); s2=sum(m2);
        if s1<1e-14||s2<1e-14, continue; end
        g=max(cumsum(m2)/s2-cumsum(m1)/s1);
        if g>1e-10, bad=true; end; wgz=max(wgz,g);
      end
      if bad, nbz=nbz+1; end
    end
    fprintf(' %3g | %.4f  %8.4f | %3d/%d   %10.2e | %3d/%d   %10.2e | %6.3f %6.3f\n',...
            gam,vm,vw,nb,J,wg,nbz,J,wgz,S1,S2);
  end
end
end
function [S,MU,AP]=run(R,beta,gam,y,Pi,nu,J,ag)
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
