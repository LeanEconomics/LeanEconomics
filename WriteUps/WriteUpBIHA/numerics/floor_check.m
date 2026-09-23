% Route 3 numerics: how far do the PRIMITIVE consumption bounds certify a variance floor?
function floor_check
beta=0.96; rho=0.9; sigma=0.4; nz=7; r=0.040; R=1+r;
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); p=abs(V(:,k)); p=p/sum(p);
y=exp(xg)'; y=y/(p'*y); ymin=min(y); ymax=max(y);
amax=6000; na=2000; ag=[0; exp(linspace(log(1e-3),log(amax),na-1))'];
for gamma=[1 3]
  fprintf('\n==================== gamma = %d, r = %.3f, betaR = %.5f\n',gamma,r,beta*R);
  [c,ap,kappa]=solve_egm(R,beta,gamma,y,Pi,ag); Th=(beta*R)^(1/gamma); s=kappa*R;
  fprintf('kappa=%.4f Thorn=%.5f s=kappa R=%.4f\n',kappa,Th,s);
  fprintf('y      = %s\n',mat2str(y',3)); fprintf('c(0,z) = %s\n',mat2str(c(1,:),3));
  fprintf('ap(0,z)= %s\n',mat2str(ap(1,:),3));
  % primitive floor at zero wealth: f >= Psi(f), Psi(f)(z)=min(y_z,(M_{-g,pi(z,.)}(f)+s y_z)/(Th+s))
  f=ymin*ones(nz,1);
  for it=1:500
    M=((Pi*(f.^(-gamma)))).^(-1/gamma); fn=min(y,(M+s*y)/(Th+s)); if max(abs(fn-f))<1e-12, break; end; f=fn;
  end
  fprintf('f*(z)  = %s   (primitive floor at a=0; truth above)\n',mat2str(f',3));
  % state-dependent sandwich upper bound: c <= kappa(m + H(z)), R H = P y + P H
  H=(R*eye(nz)-Pi)\(Pi*y); fprintf('H(z)   = %s  kappa H = %s\n',mat2str(H',3),mat2str(kappa*H',3));
  for a=[0 1 2 4 6]
    k=find(ag>=a,1); m=R*ag(k)+y';
    fprintf('  a=%g: truth c=%s\n        upper min(m,k(m+H))=%s\n        lower f*+s a=%s\n',ag(k),mat2str(c(k,:),3),mat2str(min(m,kappa*(m+H')),3),mat2str(f'+s*ag(k),3));
  end
  % true conditional variance of u'(c(a',z')) given z, as a function of a'
  up=c.^(-gamma); Eu=up*Pi'; Eu2=(up.^2)*Pi'; Var=Eu2-Eu.^2;  % na x nz (columns: today's z)
  fprintf('true min_z Var(u''(c(a'',z''))|z) at a''= 0,0.5,1,2,4,5,8: %s\n',mat2str(arrayfun(@(a) min(Var(find(ag>=a,1),:)),[0 .5 1 2 4 5 8]),2));
  normM=max(up(:)); fprintf('||M||^2 = %.3g ; floor within 10%% of A0 needs 1-betaR < 0.1 v0/(2||M||^2) = %.2e (v0 at a''<=5)\n',normM^2,0.1*min(min(Var(ag<=5,:)))/(2*normM^2));
  % certified pair gap from the primitive bounds
  Acert=0; for k=1:na
    a=ag(k); m=R*a+y'; U=min(m,kappa*(m+H')); L=f'+s*a; ok=true; vcert=inf;
    for z=1:nz
      best=0;
      for z1=1:nz, for z2=1:nz
        g=U(z1)^(-gamma)-L(z2)^(-gamma); if g>0, best=max(best,min(Pi(z,z1),Pi(z,z2))/2*g^2); end
      end, end
      if best<=0, ok=false; break; end; vcert=min(vcert,best);
    end
    if ~ok, break; end; Acert=a; vlast=vcert;
  end
  fprintf('certified variance floor holds for a'' <= %.3f (then v0 = %.2e); needed A0 ~ 4.6\n',Acert,vlast);
end
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
function [c,ap,kappa]=solve_egm(R,beta,gamma,y,Pi,ag)
nz=numel(y); na=numel(ag); kappa=1-(beta*R)^(1/gamma)/R;
m=y'+R*ag; c=kappa*m + kappa*max(y)/(R-1); c=min(c,m);
for it=1:100000
  up=c.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cnew=zeros(na,nz);
  for z=1:nz
    cnew(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap'); corner=m(:,z)<mend(1,z); cnew(corner,z)=m(corner,z);
  end
  cnew=min(cnew,m); err=max(abs(cnew(:).^(-gamma)-c(:).^(-gamma))./c(:).^(-gamma)); c=cnew; if err<1e-10, break; end
end
ap=m-c;
end
