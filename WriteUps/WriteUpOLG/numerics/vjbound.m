% A primitive bound on V_k(z) = sup_a (Theorem-1 failure at earnings state z, stage k).
%
% Derivation (no power mean, so no superadditivity obstruction).  Suppose the failure
% D = c2 - c1 - dr*a > 0 at (a,z).  Then b1 > b2 >= 0, so the r1 Euler holds above the floor and the
% r2 Euler under the cap:
%     b*R2*sum pi C2(z',b2)^-g <= c2^-g ,      c1^-g <= b*R1*sum pi C1(z',b1)^-g .
% Stage-k failure bound eps_k and monotonicity of C1 in assets give
%     C2(z',b2) <= C1(z',b1) + dr*b1 + eps_k(z'),
% and (C+s)^-g = C^-g (1+s/C)^-g >= C^-g (1+sig)^-g with sig = max_z' s(z')/C1(z',b1).  Hence
%     c2 <= c1 (1+sig) (R1/R2)^(1/g),
%     D <= c1 [ (R1/R2)^(1/g) (1+sig) - 1 ] - dr*a     =: Dbnd.
% V_{k}(z) = sup_a Dbnd^+ , and the recursion eps_{k+1} = V_{k+1} starts from eps_0 = 0 (exact).
function vjbound
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; alpha=9/25; delta=2/25;
[Pi,y,nu]=tauchen(rho,sigma,nz);
D=@(r) alpha/((1-alpha)*(r+delta));
na=500; ag=[0; exp(linspace(log(1e-3),log(4000),na-1))'];
for pr=[0.04 0.06]'
end
for pp=1:2
  if pp==1, r1=0.04; r2=0.06; else, r1=0.02; r2=0.08; end
  R1=1+r1; R2=1+r2; dr=r2-r1; budget=D(r1)-D(r2);
  fprintf('\n######## r1=%.2f r2=%.2f, budget %.4f ########\n',r1,r2,budget);
  for gam=[5 8]
    c1f=egm(R1,beta,gam,y,Pi,ag,J); c2f=egm(R2,beta,gam,y,Pi,ag,J);
    m1=y'+R1*ag; m2=y'+R2*ag;
    Th=(beta*R2)^(1/gam); kap=zeros(J,1); kap(1)=1;
    for k=1:J-1, kap(k+1)=kap(k)*R2/(Th+kap(k)*R2); end
    q=(R1/R2)^(1/gam);
    for mode=1:2                         % 1 = true C1, 2 = sandwich floor on C1
      eps=zeros(nz,J);                   % eps(z,k+1) = V_k(z)
      for k=1:J-1
        ebar=max(eps(:,k));
        for z=1:nz
          b1=max(m1(:,z)-c1f{k+1}(:,z),0); c1=c1f{k+1}(:,z);
          v=-inf;
          for i=1:na
            if b1(i)<=0, continue; end
            % next period's consumption at b1, state z'
            if mode==1
              Cn=interp1(ag,c1f{k}(:,1),b1(i),'linear','extrap');  % placeholder, per z' below
              Cn=zeros(nz,1);
              for zp=1:nz, Cn(zp)=interp1(ag,c1f{k}(:,zp),b1(i),'linear','extrap'); end
            else
              Cn=kap(k)*(y+R1*b1(i));
            end
            s=dr*b1(i)+eps(:,k);
            sig=max(s./Cn);
            v=max(v,c1(i)*(q*(1+sig)-1)-dr*ag(i));
          end
          eps(z,k+1)=max(0,v);
        end
      end
      % nu-weighted, accumulated
      L=zeros(J,1); for j=1:J, L(j)=(1-kap(J-j+1))*R2; end
      Bz=zeros(J,1); for j=1:J, Bz(j)=nu'*eps(:,J-j+1); end
      acc=accumEps(L,Bz,J);
      nm={'true C1  ','sandwich C1'};
      fprintf(' gamma=%g %s : V by state (stage J-1) ',gam,nm{mode});
      fprintf('%9.4f',eps(:,J)); fprintf('\n');
      fprintf('            nu-weighted max_j %.5f, accumulated %.4f  %s\n',...
              max(Bz),acc,tick(acc<budget));
    end
  end
end
end
function B=accumEps(L,ep,J)
e=0; tot=0;
for j=1:J, tot=tot+e; if j<J, e=L(j)*e+ep(j); end, end
B=tot/J;
end
function s=tick(b), if b, s='PASS'; else, s='fail'; end, end
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
