% The closed form for Phi at the plan's OWN price, from the Euler equation and the budget.
%   m_t = beta^t u'(c_t) is a state-price density: E_t[m_{t+1}] = m_t / R   (interior).
%   (i)   P[s] = 0          with  s_t = w y_t - c_t,  P[x] = sum_t E[m_t x_t]
%   (ii)  P[a] = -(1/R) P_1[s],  P_1[x] = sum_t t E[m_t x_t]
%   =>    Phi = P[a] - K P[y] = (wY/R)(T_c - T_y) - K Y,   Y = P[y], T_c = P_1[c]/P[c], etc.
function mfgdur
alpha=9/25; delta=2/25; J=60; rho=0.9; sigma=0.4; nz=7; beta=0.96;
[y,Pi,nu]=shocks(rho,sigma,nz);
na=800; ag=[0; exp(linspace(log(1e-3),log(4000),na-1))'];
fprintf(' gam   K      P[s]/P[c]   P[a]+P1[s]/R   Phi (direct)   Phi (duration form)   T_c     T_y    constrained\n');
for gam=[1 2 3 5]
  rst=eqrate(beta,gam,alpha,delta,y,Pi,nu,J,ag); Kst=(alpha/(rst+delta))^(1/(1-alpha));
  for f=[0.9 1.0 1.1]
    K=Kst*f; r=alpha*K^(alpha-1)-delta; w=(1-alpha)*K^alpha; R=1+r;
    [~,MU,AP]=supply(R,beta,gam,y,Pi,nu,J,ag);
    Pa=0; Ps=0; P1s=0; Py=0; Pc=0; P1c=0; P1y=0; Phi=0; con=0;
    for j=1:J
      t=j-1; mu=MU(:,:,j); ap=AP(:,:,j);
      for z=1:nz
        a=w*ag; s0=w*ap(:,z); c=w*y(z)+R*a-s0; ok=c>1e-12;
        m=beta^t*c.^(-gam); ms=m.*mu(:,z);
        Pa =Pa +sum(ms(ok).*a(ok));         Py =Py +sum(ms(ok))*y(z);
        Pc =Pc +sum(ms(ok).*c(ok));         P1c=P1c+t*sum(ms(ok).*c(ok));
        P1y=P1y+t*sum(ms(ok))*y(z);
        sf=w*y(z)-c;  Ps=Ps+sum(ms(ok).*sf(ok));  P1s=P1s+t*sum(ms(ok).*sf(ok));
        Phi=Phi+sum(ms(ok).*(a(ok)-K*y(z)));
        con=con+sum(mu(s0<1e-12 & ok,z));
      end
    end
    Tc=P1c/Pc; Ty=P1y/Py;
    dur=(w*Py/R)*(Tc-Ty)-K*Py;
    fprintf(' %3g %6.3f | Pa %.6e  Py %.6e  Pc %.6e  wPy %.6e | P[s]/Pc %+.3e | Pa+P1s/R %+.4e\n',...
            gam,K,Pa,Py,Pc,w*Py,Ps/Pc,Pa+P1s/R);
    fprintf('           | Tc %.10f  Ty %.10f  Tc-Ty %.3e | Phi %.6e  dur %.6e  gap %.2e | constr %.3f\n',...
            Tc,Ty,Tc-Ty,Phi,dur,abs(Phi-dur),con/J);
  end
end
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
