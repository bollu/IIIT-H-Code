class UserController < ApplicationController
  before_action  :kick_out_unauthorized?
  

  def signup
    if not request.post? then
        return
    end

    if params[:password_confirmation] != params[:password] then
        flash[:error] = "Passwords do not match"
        redirect_to 'user#signup'
    end

    @user = User.new(user_params)

    if @user.save then
        session["user_id"] = @user.id 
        session["username"] = @user.username 
        redirect_to :controller => 'user', :action => 'mainpage'
    else
        flash[:error] = @user.errors
        redirect_to :controller => 'user', :action => 'signup'
    end
  end

  # use this to kick out unauthorized profiles
  def kick_out_unauthorized?
    @unauthorized_allowed_actions = ['signup', 'login']
    
    if @unauthorized_allowed_actions.include?(params[:action]) then
      return
    end

    # if there is a session ID and the user exists, then allow continue
    if session.has_key?("user_id") and session.has_key?("username") then
      @user = User.find_by("username": session[:username])

      if not @user.nil? and @user.id == session["user_id"] then
        return
      else
        session["user_id"] = nil
      end
    end

    # if not, send back to login 
    redirect_to :controller => 'user', :action => 'login'
  end


  # Use this to automatically redirect to an authorized page
  def auto_redirect_authorized?
    if session.has_key?("user_id") then
      redirect_to_action = "mainpage"
      if params.has_key?(:redirect_to) then
        redirect_to_action = params[:redirect_to]
      end
      redirect_to :controller => 'user', :action => redirect_to_action
    end
  end
  

  def logout
    session[:user_id] = nil
    redirect_to :controller => 'user', :action => 'login'
  end


  def login
    if auto_redirect_authorized? then
      return
    end

   if not request.post? then
        return
    end

 
    @user = User.find_by(username: user_params[:username])

    if @user.nil? then
      flash[:error] = {"username": ['does not exist']}
      redirect_to :controller => 'user', :action => 'login'
    elsif !@user.authenticate(user_params[:password]) then
      flash[:error] = {"password": ["maybe incorrect"], "username": ["maybe incorrect"]}
      redirect_to :controller => 'user', :action => 'login'
    else
      session["user_id"] = @user.id
      session["username"] = @user.username
      # TODO: allow custom redirects here
      redirect_to :controller => 'user', :action => 'mainpage'
    end
  end

  def user_params
    params.require(:user).permit(:name, :email, :username, :password, :password_conformation)
  end

end
