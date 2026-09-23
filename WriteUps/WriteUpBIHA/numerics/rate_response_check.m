% Numerical check of the slack elasticity condition and the rate-response induction
% Aiyagari (1994) gamma=3, beta=0.96, Tauchen rho=0.9 sigma=0.4, borrowing limit 0.
function rate_response_check(outdir)
gamma=3; beta=0.96; rho=0.9; sigma=0.4; nz=7;
r1=0.040; r2=0.041; R1=1+r1; R2=1+r2; dr=r2-r1;
% --- Tauchen on log income, unconditional sd sigma, innovation sd sigma*sqrt(1-rho^2)
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); p=abs(V(:,k)); p=p/sum(p);
y=exp(xg)'; y=y/(p'*y);            % mean income 1 (column nz x 1)
ymin=min(y); ymax=max(y);
fprintf('income states (mean 1): %s\n', mat2str(y',4));
% --- asset grid (units: mean income), log-spaced to cover the support
amax=6000; na=2000; ag=[0; exp(linspace(log(1e-3),log(amax),na-1))'];
% --- solve both economies by EGM
[c1,ap1,kappa1]=solve_egm(R1,beta,gamma,y,Pi,ag);
[c2,ap2,kappa2]=solve_egm(R2,beta,gamma,y,Pi,ag);
Th1=(beta*R1)^(1/gamma); Th2=(beta*R2)^(1/gamma);
fprintf('betaR1=%.5f  kappa1=%.5f  Thorn1=%.5f | betaR2=%.5f kappa2=%.5f\n',beta*R1,kappa1,Th1,beta*R2,kappa2);
% support: fixed point of ap in top state
ia=find(ap1(:,nz)<ag,1,'first'); fprintf('top-state dissaving starts at a = %.0f (mean-income units)\n',ag(ia));
% --- 2. elasticity condition (c2/c1)^gamma <= R2/R1, per state
EC=(c2./c1).^gamma; fprintf('\nEC fails (first grid point) per income state:\n');
for z=1:nz, k=find(EC(:,z)>R2/R1,1,'first'); if isempty(k), fprintf('  z=%d: holds everywhere\n',z); else fprintf('  z=%d: fails from a=%.1f\n',z,ag(k)); end, end
% --- 3. slack condition at pivots b=ap1(a,z): max_z' (c2(b,z')/c1(b,z'))^g <= (R2/R1)(1+dr a/c1(a,z))^g
lhs=zeros(na,nz); rhs=zeros(na,nz);
for z=1:nz
  b=ap1(:,z); c1b=interp_cols(ag,c1,b); c2b=interp_cols(ag,c2,b);
  lhs(:,z)=max((c2b./c1b).^gamma,[],2);
  rhs(:,z)=(R2/R1)*(1+dr*ag./c1(:,z)).^gamma;
end
marg=(log(rhs)-log(lhs))/dr;   % log-margin per unit dr
[mm,im]=min(marg(:)); [ia,iz]=ind2sub(size(marg),im);
fprintf('\nSEC log-margin per unit dr: min %.2f at a=%.2f z=%d; median %.1f; tail (a>1000) min %.1f\n',mm,ag(ia),iz,median(marg(:)),min(min(marg(ag>1000,:))));
fprintf('SEC holds everywhere: %d\n', all(marg(:)>0));
% --- 4. rate-response bound: c2-c1 <= dr (alpha a + B)
gap=(c2-c1)/dr; alpha0=1-(1-kappa1)/gamma;
fprintf('\nalpha0 = 1-(1-kappa)/gamma = %.4f ; Thorn2 = %.5f\n',alpha0,Th2);
for eps=[0 0.02 0.05 0.1]
  al=alpha0+eps; Bneed=max(max(gap-al*ag)); fprintf('  alpha=%.4f: smallest B on grid = %.3f (gap at a=0: %s)\n',al,Bneed,mat2str(gap(1,:),3));
end
% empirical slope of the gap in the tail
sl=(gap(end,:)-gap(end-200,:))./(ag(end)-ag(end-200)); fprintf('  empirical tail slope of gap: %s\n',mat2str(sl,4));
% --- 5. induction step with the exact Euler transfer
%  IH at tomorrow's states: c2(a2',z') <= c1(a2',z') + dr(alpha a2' + B).  Transfer:
%  c2bound(a,z) = (R1/R2)^(1/g) c1(a,z) [ E c1(a1',z')^-g / E (c1(a1',z')+X_z')^-g ]^(1/g),
%  X_z' = c1(a2',z') - c1(a1',z') + dr(alpha a2' + B)  (true policies)
al=alpha0+0.05; B=max(max(gap-al*ag))*1.0;  % take the fitted B
Xmin=zeros(na,nz); ratio_exp=nan(na,nz); ratio_min=nan(na,nz);
for z=1:nz
  a1=ap1(:,z); a2=ap2(:,z);
  c1a1=interp_cols(ag,c1,a1); c1a2=interp_cols(ag,c1,a2);
  X=(c1a2-c1a1)+dr*(al*a2+B); X=max(X,0);           % na x nz (over z')
  pz=Pi(z,:);
  Eu=(c1a1.^(-gamma))*pz'; EuX=((c1a1+X).^(-gamma))*pz';
  cb_exp=(R1/R2)^(1/gamma)*c1(:,z).*(Eu./EuX).^(1/gamma);
  cmin=min(c1a1,[],2); Xmax=max(X,[],2);
  cb_min=(R1/R2)^(1/gamma)*c1(:,z).*(1+Xmax./cmin);
  bound=dr*(al*ag+B); int=a1>1e-9;
  ratio_exp(int,z)=(cb_exp(int)-c1(int,z))./bound(int);
  ratio_min(int,z)=(cb_min(int)-c1(int,z))./bound(int);
end
fprintf('\nInduction step (alpha=%.4f, B=%.3f): max ratio (exact expectation) = %.3f, (min version) = %.3f\n',al,B,max(ratio_exp(:)),max(ratio_min(:)));
for z=1:nz, k=find(ratio_exp(:,z)>1); if isempty(k), fprintf('  z=%d: closes on all interior states\n',z); else fprintf('  z=%d: FAILS at a in [%.2f, %.2f] (%d pts), worst ratio %.2f\n',z,ag(min(k)),ag(max(k)),numel(k),max(ratio_exp(:,z))); end, end
% also: does the truth satisfy the bound where the step fails? (sanity)
% --- figure
f=figure('visible','off','position',[0 0 1100 800]);
subplot(2,2,1); semilogx(ag(2:end),marg(2:end,:)); hold on; yline(0,'k'); xlabel('assets (mean income=1)'); ylabel('SEC log-margin / dr'); title('Slack condition margin at pivots'); ylim([-5 60]);
subplot(2,2,2); semilogx(ag(2:end),log(EC(2:end,:))/dr); hold on; yline(log(R2/R1)/dr,'k--'); xlabel('b'); ylabel('log(c_2/c_1)^\gamma / dr'); title('Elasticity condition (dashed = allowed)'); ylim([-40 80]);
subplot(2,2,3); semilogx(ag(2:end),gap(2:end,:)); hold on; semilogx(ag(2:end),al*ag(2:end)+B,'k--'); xlabel('a'); ylabel('(c_2-c_1)/dr'); title('Rate response of consumption vs linear bound');
subplot(2,2,4); semilogx(ag(2:end),ratio_exp(2:end,:)); hold on; yline(1,'k'); xlabel('a'); ylabel('bound ratio'); title('Induction step: exact-expectation transfer'); ylim([0 2]);
saveas(f,fullfile(outdir,'rate_response.png'));
save(fullfile(outdir,'rate_response.mat'),'ag','c1','c2','ap1','ap2','marg','EC','gap','ratio_exp','ratio_min','y','Pi');
end

function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end

function [c,ap,kappa]=solve_egm(R,beta,gamma,y,Pi,ag)
nz=numel(y); na=numel(ag); kappa=1-(beta*R)^(1/gamma)/R;
m=y'+R*ag;                      % cash on hand, na x nz
c=kappa*m + kappa*max(y)/(R-1); c=min(c,m); % start inside the sandwich
for it=1:100000
  up=c.^(-gamma);                % u'(c(a',z')) on grid a'
  rhs=beta*R*(up*Pi');           % na x nz : E[u'(c(a',z'))|z]  (rows a', cols z)
  cend=rhs.^(-1/gamma);          % consumption today implied by saving a'
  mend=cend+ag;                  % endogenous cash on hand
  cnew=zeros(na,nz);
  for z=1:nz
    mz=mend(:,z); cz=cend(:,z);
    cnew(:,z)=interp1(mz,cz,m(:,z),'linear','extrap');
    corner=m(:,z)<mz(1); cnew(corner,z)=m(corner,z);   % a'=0 binds
  end
  cnew=min(cnew,m);
  err=max(abs(cnew(:).^(-gamma)-c(:).^(-gamma))./c(:).^(-gamma));
  c=cnew; if err<1e-10, break; end
end
fprintf('EGM at R=%.4f: %d iterations, rel u'' error %.1e\n',R,it,err);
ap=m-c;
end

function out=interp_cols(ag,c,b)
% interpolate each column of c (na x nz, on grid ag) at the points b (na x 1) -> na x nz
nz=size(c,2); out=zeros(numel(b),nz);
for z=1:nz, out(:,z)=interp1(ag,c(:,z),b,'linear','extrap'); end
end
